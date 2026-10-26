import V185TrunkScan23Chunk0501

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2968788 : List Nat := [2, 4, 1, 4, 1, 2, 1, 3, 5]
def baseStart_2968788 : Nat := 118140960795 + 2968788 * 2 ^ 59
def prefixEnd_2968788 : Nat := 4983230072969 + 3 ^ 40 * 2968788 * 2
def baseEnd_2968788 : Nat := 169379467255581759666311

theorem tailTrace_2968788 : CollatzResearch.WordTrace tailWord_2968788 prefixEnd_2968788 169379467255581759666311 := by
  unfold tailWord_2968788
  simp only [CollatzResearch.WordTrace]
  refine ⟨54140296984297789734449509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72187062645730386312599345 54140296984297789734449509)
  ·
    refine ⟨10151305684555835575209283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54140296984297789734449509 10151305684555835575209283)
    ·
      refine ⟨15226958526833753362813925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151305684555835575209283 15226958526833753362813925)
      ·
        refine ⟨2855054723781328755527611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15226958526833753362813925 2855054723781328755527611)
        ·
          refine ⟨4282582085671993133291417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855054723781328755527611 4282582085671993133291417)
          ·
            refine ⟨3211936564253994849968563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4282582085671993133291417 3211936564253994849968563)
            ·
              refine ⟨4817904846380992274952845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3211936564253994849968563 4817904846380992274952845)
              ·
                refine ⟨1806714317392872103107317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4817904846380992274952845 1806714317392872103107317)
                ·
                  refine ⟨169379467255581759666311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1806714317392872103107317 169379467255581759666311)
                  ·
                    rfl

theorem cell23_2968788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 3, 5].length) (baseStart_2968788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968788 prefixEnd_2968788 := by exact prefixLift 2968788
  have htrace : WordTrace (prefixWord ++ tailWord_2968788) baseStart_2968788 baseEnd_2968788 := by
    simpa [prefixWord, tailWord_2968788, baseEnd_2968788] using wordTrace_append hprefix tailTrace_2968788
  have hstable : (prefixWord ++ tailWord_2968788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968788).length < 2 ^ (prefixWord ++ tailWord_2968788).sum := by decide
  have hdescent : baseEnd_2968788 < baseStart_2968788 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968814 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 3, 4]
def baseStart_2968814 : Nat := 118140960795 + 2968814 * 2 ^ 59
def prefixEnd_2968814 : Nat := 4983230072969 + 3 ^ 40 * 2968814 * 2
def baseEnd_2968814 : Nat := 508142851932417578423893

theorem tailTrace_2968814 : CollatzResearch.WordTrace tailWord_2968814 prefixEnd_2968814 508142851932417578423893 := by
  unfold tailWord_2968814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535192783312673238668187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72187694844334257272896997 13535192783312673238668187)
  ·
    refine ⟨20302789174969009858002281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13535192783312673238668187 20302789174969009858002281)
    ·
      refine ⟨15227091881226757393501711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20302789174969009858002281 15227091881226757393501711)
      ·
        refine ⟨22840637821840136090252567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227091881226757393501711 22840637821840136090252567)
        ·
          refine ⟨34260956732760204135378851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22840637821840136090252567 34260956732760204135378851)
          ·
            refine ⟨51391435099140306203068277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34260956732760204135378851 51391435099140306203068277)
            ·
              refine ⟨4817947040544403706537651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51391435099140306203068277 4817947040544403706537651)
              ·
                refine ⟨7226920560816605559806477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4817947040544403706537651 7226920560816605559806477)
                ·
                  refine ⟨2710095210306227084927429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7226920560816605559806477 2710095210306227084927429)
                  ·
                    refine ⟨508142851932417578423893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710095210306227084927429 508142851932417578423893)
                    ·
                      rfl

theorem cell23_2968814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 3, 4].length) (baseStart_2968814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968814 prefixEnd_2968814 := by exact prefixLift 2968814
  have htrace : WordTrace (prefixWord ++ tailWord_2968814) baseStart_2968814 baseEnd_2968814 := by
    simpa [prefixWord, tailWord_2968814, baseEnd_2968814] using wordTrace_append hprefix tailTrace_2968814
  have hstable : (prefixWord ++ tailWord_2968814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968814).length < 2 ^ (prefixWord ++ tailWord_2968814).sum := by decide
  have hdescent : baseEnd_2968814 < baseStart_2968814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968874 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 3, 5]
def baseStart_2968874 : Nat := 118140960795 + 2968874 * 2 ^ 59
def prefixEnd_2968874 : Nat := 4983230072969 + 3 ^ 40 * 2968874 * 2
def baseEnd_2968874 : Nat := 508153121545507500173801

theorem tailTrace_2968874 : CollatzResearch.WordTrace tailWord_2968874 prefixEnd_2968874 508153121545507500173801 := by
  unfold tailWord_2968874
  simp only [CollatzResearch.WordTrace]
  refine ⟨27070932661571004039132419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72189153764189344104353117 27070932661571004039132419)
  ·
    refine ⟨40606398992356506058698629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27070932661571004039132419 40606398992356506058698629)
    ·
      refine ⟨7613699811066844886005993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40606398992356506058698629 7613699811066844886005993)
      ·
        refine ⟨5710274858300133664504495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7613699811066844886005993 5710274858300133664504495)
        ·
          refine ⟨8565412287450200496756743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710274858300133664504495 8565412287450200496756743)
          ·
            refine ⟨12848118431175300745135115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565412287450200496756743 12848118431175300745135115)
            ·
              refine ⟨19272177646762951117702673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12848118431175300745135115 19272177646762951117702673)
              ·
                refine ⟨14454133235072213338277005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19272177646762951117702673 14454133235072213338277005)
                ·
                  refine ⟨5420299963152080001853877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14454133235072213338277005 5420299963152080001853877)
                  ·
                    refine ⟨508153121545507500173801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5420299963152080001853877 508153121545507500173801)
                    ·
                      rfl

theorem cell23_2968874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_2968874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968874 prefixEnd_2968874 := by exact prefixLift 2968874
  have htrace : WordTrace (prefixWord ++ tailWord_2968874) baseStart_2968874 baseEnd_2968874 := by
    simpa [prefixWord, tailWord_2968874, baseEnd_2968874] using wordTrace_append hprefix tailTrace_2968874
  have hstable : (prefixWord ++ tailWord_2968874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968874).length < 2 ^ (prefixWord ++ tailWord_2968874).sum := by decide
  have hdescent : baseEnd_2968874 < baseStart_2968874 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968887 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 8, 4]
def baseStart_2968887 : Nat := 118140960795 + 2968887 * 2 ^ 59
def prefixEnd_2968887 : Nat := 4983230072969 + 3 ^ 40 * 2968887 * 2
def baseEnd_2968887 : Nat := 508155346628343649886281

theorem tailTrace_2968887 : CollatzResearch.WordTrace tailWord_2968887 prefixEnd_2968887 508155346628343649886281 := by
  unfold tailWord_2968887
  simp only [CollatzResearch.WordTrace]
  refine ⟨108284204795236919376752915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72189469863491279584501943 108284204795236919376752915)
  ·
    refine ⟨162426307192855379065129373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108284204795236919376752915 162426307192855379065129373)
    ·
      refine ⟨60909865197320767149423515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162426307192855379065129373 60909865197320767149423515)
      ·
        refine ⟨91364797795981150724135273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60909865197320767149423515 91364797795981150724135273)
        ·
          refine ⟨68523598346985863043101455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91364797795981150724135273 68523598346985863043101455)
          ·
            refine ⟨102785397520478794564652183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68523598346985863043101455 102785397520478794564652183)
            ·
              refine ⟨154178096280718191846978275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102785397520478794564652183 154178096280718191846978275)
              ·
                refine ⟨231267144421077287770467413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154178096280718191846978275 231267144421077287770467413)
                ·
                  refine ⟨2710161848684499466060165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 231267144421077287770467413 2710161848684499466060165)
                  ·
                    refine ⟨508155346628343649886281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710161848684499466060165 508155346628343649886281)
                    ·
                      rfl

theorem cell23_2968887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 8, 4].length) (baseStart_2968887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968887 prefixEnd_2968887 := by exact prefixLift 2968887
  have htrace : WordTrace (prefixWord ++ tailWord_2968887) baseStart_2968887 baseEnd_2968887 := by
    simpa [prefixWord, tailWord_2968887, baseEnd_2968887] using wordTrace_append hprefix tailTrace_2968887
  have hstable : (prefixWord ++ tailWord_2968887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968887).length < 2 ^ (prefixWord ++ tailWord_2968887).sum := by decide
  have hdescent : baseEnd_2968887 < baseStart_2968887 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968894 : List Nat := [4, 2, 1, 2, 1, 1, 1, 3, 3, 1, 4]
def baseStart_2968894 : Nat := 118140960795 + 2968894 * 2 ^ 59
def prefixEnd_2968894 : Nat := 4983230072969 + 3 ^ 40 * 2968894 * 2
def baseEnd_2968894 : Nat := 1524469634249612422271311

theorem tailTrace_2968894 : CollatzResearch.WordTrace tailWord_2968894 prefixEnd_2968894 1524469634249612422271311 := by
  unfold tailWord_2968894
  simp only [CollatzResearch.WordTrace]
  refine ⟨13535557513276444946532217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72189640070807706381505157 13535557513276444946532217)
  ·
    refine ⟨10151668134957333709899163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13535557513276444946532217 10151668134957333709899163)
    ·
      refine ⟨15227502202436000564848745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151668134957333709899163 15227502202436000564848745)
      ·
        refine ⟨11420626651827000423636559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15227502202436000564848745 11420626651827000423636559)
        ·
          refine ⟨17130939977740500635454839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11420626651827000423636559 17130939977740500635454839)
          ·
            refine ⟨25696409966610750953182259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17130939977740500635454839 25696409966610750953182259)
            ·
              refine ⟨38544614949916126429773389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25696409966610750953182259 38544614949916126429773389)
              ·
                refine ⟨14454230606218547411165021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38544614949916126429773389 14454230606218547411165021)
                ·
                  refine ⟨5420336477331955279186883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14454230606218547411165021 5420336477331955279186883)
                  ·
                    refine ⟨8130504715997932918780325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5420336477331955279186883 8130504715997932918780325)
                    ·
                      refine ⟨1524469634249612422271311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8130504715997932918780325 1524469634249612422271311)
                      ·
                        rfl

theorem cell23_2968894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_2968894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968894 prefixEnd_2968894 := by exact prefixLift 2968894
  have htrace : WordTrace (prefixWord ++ tailWord_2968894) baseStart_2968894 baseEnd_2968894 := by
    simpa [prefixWord, tailWord_2968894, baseEnd_2968894] using wordTrace_append hprefix tailTrace_2968894
  have hstable : (prefixWord ++ tailWord_2968894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968894).length < 2 ^ (prefixWord ++ tailWord_2968894).sum := by decide
  have hdescent : baseEnd_2968894 < baseStart_2968894 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968917 : List Nat := [1, 3, 2, 2, 3, 2, 10]
def baseStart_2968917 : Nat := 118140960795 + 2968917 * 2 ^ 59
def prefixEnd_2968917 : Nat := 4983230072969 + 3 ^ 40 * 2968917 * 2
def baseEnd_2968917 : Nat := 18820758571662541139305

theorem tailTrace_2968917 : CollatzResearch.WordTrace tailWord_2968917 prefixEnd_2968917 18820758571662541139305 := by
  unfold tailWord_2968917
  simp only [CollatzResearch.WordTrace]
  refine ⟨108285298985128234500345005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72190199323418823000230003 108285298985128234500345005)
  ·
    refine ⟨40606987119423087937629377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108285298985128234500345005 40606987119423087937629377)
    ·
      refine ⟨30455240339567315953222033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40606987119423087937629377 30455240339567315953222033)
      ·
        refine ⟨22841430254675486964916525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30455240339567315953222033 22841430254675486964916525)
        ·
          refine ⟨8565536345503307611843697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22841430254675486964916525 8565536345503307611843697)
          ·
            refine ⟨6424152259127480708882773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8565536345503307611843697 6424152259127480708882773)
            ·
              refine ⟨18820758571662541139305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6424152259127480708882773 18820758571662541139305)
              ·
                rfl

theorem cell23_2968917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 2, 10].length) (baseStart_2968917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968917 prefixEnd_2968917 := by exact prefixLift 2968917
  have htrace : WordTrace (prefixWord ++ tailWord_2968917) baseStart_2968917 baseEnd_2968917 := by
    simpa [prefixWord, tailWord_2968917, baseEnd_2968917] using wordTrace_append hprefix tailTrace_2968917
  have hstable : (prefixWord ++ tailWord_2968917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968917).length < 2 ^ (prefixWord ++ tailWord_2968917).sum := by decide
  have hdescent : baseEnd_2968917 < baseStart_2968917 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968928 : List Nat := [2, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2]
def baseStart_2968928 : Nat := 118140960795 + 2968928 * 2 ^ 59
def prefixEnd_2968928 : Nat := 4983230072969 + 3 ^ 40 * 2968928 * 2
def baseEnd_2968928 : Nat := 1524487092591865289246155

theorem tailTrace_2968928 : CollatzResearch.WordTrace tailWord_2968928 prefixEnd_2968928 1524487092591865289246155 := by
  unfold tailWord_2968928
  simp only [CollatzResearch.WordTrace]
  refine ⟨54142850094044191689497719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72190466792058922252663625 54142850094044191689497719)
  ·
    refine ⟨81214275141066287534246579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54142850094044191689497719 81214275141066287534246579)
    ·
      refine ⟨121821412711599431301369869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81214275141066287534246579 121821412711599431301369869)
      ·
        refine ⟨45683029766849786738013701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121821412711599431301369869 45683029766849786738013701)
        ·
          refine ⟨8565568081284335013377569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45683029766849786738013701 8565568081284335013377569)
          ·
            refine ⟨6424176060963251260033177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8565568081284335013377569 6424176060963251260033177)
            ·
              refine ⟨4818132045722438445024883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424176060963251260033177 4818132045722438445024883)
              ·
                refine ⟨7227198068583657667537325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818132045722438445024883 7227198068583657667537325)
                ·
                  refine ⟨2710199275718871625326497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7227198068583657667537325 2710199275718871625326497)
                  ·
                    refine ⟨2032649456789153718994873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2710199275718871625326497 2032649456789153718994873)
                    ·
                      refine ⟨1524487092591865289246155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032649456789153718994873 1524487092591865289246155)
                      ·
                        rfl

theorem cell23_2968928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 2, 2, 1, 3, 2, 2].length) (baseStart_2968928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968928 prefixEnd_2968928 := by exact prefixLift 2968928
  have htrace : WordTrace (prefixWord ++ tailWord_2968928) baseStart_2968928 baseEnd_2968928 := by
    simpa [prefixWord, tailWord_2968928, baseEnd_2968928] using wordTrace_append hprefix tailTrace_2968928
  have hstable : (prefixWord ++ tailWord_2968928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968928).length < 2 ^ (prefixWord ++ tailWord_2968928).sum := by decide
  have hdescent : baseEnd_2968928 < baseStart_2968928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968938 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 1, 6]
def baseStart_2968938 : Nat := 118140960795 + 2968938 * 2 ^ 59
def prefixEnd_2968938 : Nat := 4983230072969 + 3 ^ 40 * 2968938 * 2
def baseEnd_2968938 : Nat := 508164075799470083373703

theorem tailTrace_2968938 : CollatzResearch.WordTrace tailWord_2968938 prefixEnd_2968938 508164075799470083373703 := by
  unfold tailWord_2968938
  simp only [CollatzResearch.WordTrace]
  refine ⟨27071516229513038771714867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72190709945368103391239645 27071516229513038771714867)
  ·
    refine ⟨40607274344269558157572301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27071516229513038771714867 40607274344269558157572301)
    ·
      refine ⟨15227727879101084309089613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40607274344269558157572301 15227727879101084309089613)
      ·
        refine ⟨5710397954662906615908605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15227727879101084309089613 5710397954662906615908605)
        ·
          refine ⟨2141399232998589980965727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5710397954662906615908605 2141399232998589980965727)
          ·
            refine ⟨3212098849497884971448591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141399232998589980965727 3212098849497884971448591)
            ·
              refine ⟨4818148274246827457172887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212098849497884971448591 4818148274246827457172887)
              ·
                refine ⟨7227222411370241185759331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818148274246827457172887 7227222411370241185759331)
                ·
                  refine ⟨10840833617055361778638997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227222411370241185759331 10840833617055361778638997)
                  ·
                    refine ⟨508164075799470083373703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10840833617055361778638997 508164075799470083373703)
                    ·
                      rfl

theorem cell23_2968938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 1, 6].length) (baseStart_2968938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968938 prefixEnd_2968938 := by exact prefixLift 2968938
  have htrace : WordTrace (prefixWord ++ tailWord_2968938) baseStart_2968938 baseEnd_2968938 := by
    simpa [prefixWord, tailWord_2968938, baseEnd_2968938] using wordTrace_append hprefix tailTrace_2968938
  have hstable : (prefixWord ++ tailWord_2968938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968938).length < 2 ^ (prefixWord ++ tailWord_2968938).sum := by decide
  have hdescent : baseEnd_2968938 < baseStart_2968938 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968941 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 4]
def baseStart_2968941 : Nat := 118140960795 + 2968941 * 2 ^ 59
def prefixEnd_2968941 : Nat := 4983230072969 + 3 ^ 40 * 2968941 * 2
def baseEnd_2968941 : Nat := 1524493767840373738383595

theorem tailTrace_2968941 : CollatzResearch.WordTrace tailWord_2968941 prefixEnd_2968941 1524493767840373738383595 := by
  unfold tailWord_2968941
  simp only [CollatzResearch.WordTrace]
  refine ⟨108286174337041286599218677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72190782891360857732812451 108286174337041286599218677)
  ·
    refine ⟨10151828844097620618676751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108286174337041286599218677 10151828844097620618676751)
    ·
      refine ⟨15227743266146430928015127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10151828844097620618676751 15227743266146430928015127)
      ·
        refine ⟨22841614899219646392022691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15227743266146430928015127 22841614899219646392022691)
        ·
          refine ⟨34262422348829469588034037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22841614899219646392022691 34262422348829469588034037)
          ·
            refine ⟨3212102095202762773878191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34262422348829469588034037 3212102095202762773878191)
            ·
              refine ⟨4818153142804144160817287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212102095202762773878191 4818153142804144160817287)
              ·
                refine ⟨7227229714206216241225931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818153142804144160817287 7227229714206216241225931)
                ·
                  refine ⟨10840844571309324361838897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227229714206216241225931 10840844571309324361838897)
                  ·
                    refine ⟨8130633428481993271379173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10840844571309324361838897 8130633428481993271379173)
                    ·
                      refine ⟨1524493767840373738383595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8130633428481993271379173 1524493767840373738383595)
                      ·
                        rfl

theorem cell23_2968941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 2, 4].length) (baseStart_2968941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968941 prefixEnd_2968941 := by exact prefixLift 2968941
  have htrace : WordTrace (prefixWord ++ tailWord_2968941) baseStart_2968941 baseEnd_2968941 := by
    simpa [prefixWord, tailWord_2968941, baseEnd_2968941] using wordTrace_append hprefix tailTrace_2968941
  have hstable : (prefixWord ++ tailWord_2968941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968941).length < 2 ^ (prefixWord ++ tailWord_2968941).sum := by decide
  have hdescent : baseEnd_2968941 < baseStart_2968941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968957 : List Nat := [1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 5]
def baseStart_2968957 : Nat := 118140960795 + 2968957 * 2 ^ 59
def prefixEnd_2968957 : Nat := 4983230072969 + 3 ^ 40 * 2968957 * 2
def baseEnd_2968957 : Nat := 1524501983530845675783521

theorem tailTrace_2968957 : CollatzResearch.WordTrace tailWord_2968957 prefixEnd_2968957 1524501983530845675783521 := by
  unfold tailWord_2968957
  simp only [CollatzResearch.WordTrace]
  refine ⟨108286757904983321331801125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72191171936655547554534083 108286757904983321331801125)
  ·
    refine ⟨20303767107184372749712711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108286757904983321331801125 20303767107184372749712711)
    ·
      refine ⟨30455650660776559124569067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20303767107184372749712711 30455650660776559124569067)
      ·
        refine ⟨45683475991164838686853601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30455650660776559124569067 45683475991164838686853601)
        ·
          refine ⟨34262606993373629015140201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45683475991164838686853601 34262606993373629015140201)
          ·
            refine ⟨25696955245030221761355151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34262606993373629015140201 25696955245030221761355151)
            ·
              refine ⟨38545432867545332642032727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25696955245030221761355151 38545432867545332642032727)
              ·
                refine ⟨57818149301317998963049091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38545432867545332642032727 57818149301317998963049091)
                ·
                  refine ⟨86727223951976998444573637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57818149301317998963049091 86727223951976998444573637)
                  ·
                    refine ⟨16261354490995687208357557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86727223951976998444573637 16261354490995687208357557)
                    ·
                      refine ⟨1524501983530845675783521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16261354490995687208357557 1524501983530845675783521)
                      ·
                        rfl

theorem cell23_2968957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 5].length) (baseStart_2968957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968957 prefixEnd_2968957 := by exact prefixLift 2968957
  have htrace : WordTrace (prefixWord ++ tailWord_2968957) baseStart_2968957 baseEnd_2968957 := by
    simpa [prefixWord, tailWord_2968957, baseEnd_2968957] using wordTrace_append hprefix tailTrace_2968957
  have hstable : (prefixWord ++ tailWord_2968957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968957).length < 2 ^ (prefixWord ++ tailWord_2968957).sum := by decide
  have hdescent : baseEnd_2968957 < baseStart_2968957 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2968971 : List Nat := [1, 1, 1, 1, 4, 3, 1, 5, 1, 3, 2]
def baseStart_2968971 : Nat := 118140960795 + 2968971 * 2 ^ 59
def prefixEnd_2968971 : Nat := 4983230072969 + 3 ^ 40 * 2968971 * 2
def baseEnd_2968971 : Nat := 1524509172260008621008457

theorem tailTrace_2968971 : CollatzResearch.WordTrace tailWord_2968971 prefixEnd_2968971 1524509172260008621008457 := by
  unfold tailWord_2968971
  simp only [CollatzResearch.WordTrace]
  refine ⟨108287268526932601722810767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72191512351288401148540511 108287268526932601722810767)
  ·
    refine ⟨162430902790398902584216151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108287268526932601722810767 162430902790398902584216151)
    ·
      refine ⟨243646354185598353876324227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162430902790398902584216151 243646354185598353876324227)
      ·
        refine ⟨365469531278397530814486341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243646354185598353876324227 365469531278397530814486341)
        ·
          refine ⟨68525537114699537027716189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365469531278397530814486341 68525537114699537027716189)
          ·
            refine ⟨25697076418012326385393571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68525537114699537027716189 25697076418012326385393571)
            ·
              refine ⟨38545614627018489578090357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25697076418012326385393571 38545614627018489578090357)
              ·
                refine ⟨3613651371282983397945971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38545614627018489578090357 3613651371282983397945971)
                ·
                  refine ⟨5420477056924475096918957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613651371282983397945971 5420477056924475096918957)
                  ·
                    refine ⟨2032678896346678161344609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5420477056924475096918957 2032678896346678161344609)
                    ·
                      refine ⟨1524509172260008621008457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032678896346678161344609 1524509172260008621008457)
                      ·
                        rfl

theorem cell23_2968971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 3, 2].length) (baseStart_2968971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2968971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2968971 prefixEnd_2968971 := by exact prefixLift 2968971
  have htrace : WordTrace (prefixWord ++ tailWord_2968971) baseStart_2968971 baseEnd_2968971 := by
    simpa [prefixWord, tailWord_2968971, baseEnd_2968971] using wordTrace_append hprefix tailTrace_2968971
  have hstable : (prefixWord ++ tailWord_2968971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2968971).length < 2 ^ (prefixWord ++ tailWord_2968971).sum := by decide
  have hdescent : baseEnd_2968971 < baseStart_2968971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2968971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969005 : List Nat := [1, 5, 2, 2, 1, 1, 3, 2, 1, 3, 2]
def baseStart_2969005 : Nat := 118140960795 + 2969005 * 2 ^ 59
def prefixEnd_2969005 : Nat := 4983230072969 + 3 ^ 40 * 2969005 * 2
def baseEnd_2969005 : Nat := 1524526630602261487983301

theorem tailTrace_2969005 : CollatzResearch.WordTrace tailWord_2969005 prefixEnd_2969005 1524526630602261487983301 := by
  unfold tailWord_2969005
  simp only [CollatzResearch.WordTrace]
  refine ⟨108288508608809425529548469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72192339072539617019698979 108288508608809425529548469)
  ·
    refine ⟨10152047682075883643395169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108288508608809425529548469 10152047682075883643395169)
    ·
      refine ⟨7614035761556912732546377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10152047682075883643395169 7614035761556912732546377)
      ·
        refine ⟨5710526821167684549409783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7614035761556912732546377 5710526821167684549409783)
        ·
          refine ⟨8565790231751526824114675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5710526821167684549409783 8565790231751526824114675)
          ·
            refine ⟨12848685347627290236172013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8565790231751526824114675 12848685347627290236172013)
            ·
              refine ⟨4818257005360233838564505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12848685347627290236172013 4818257005360233838564505)
              ·
                refine ⟨3613692754020175378923379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4818257005360233838564505 3613692754020175378923379)
                ·
                  refine ⟨5420539131030263068385069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613692754020175378923379 5420539131030263068385069)
                  ·
                    refine ⟨2032702174136348650644401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5420539131030263068385069 2032702174136348650644401)
                    ·
                      refine ⟨1524526630602261487983301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032702174136348650644401 1524526630602261487983301)
                      ·
                        rfl

theorem cell23_2969005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 3, 2].length) (baseStart_2969005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969005 prefixEnd_2969005 := by exact prefixLift 2969005
  have htrace : WordTrace (prefixWord ++ tailWord_2969005) baseStart_2969005 baseEnd_2969005 := by
    simpa [prefixWord, tailWord_2969005, baseEnd_2969005] using wordTrace_append hprefix tailTrace_2969005
  have hstable : (prefixWord ++ tailWord_2969005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969005).length < 2 ^ (prefixWord ++ tailWord_2969005).sum := by decide
  have hdescent : baseEnd_2969005 < baseStart_2969005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969007 : List Nat := [1, 1, 2, 1, 2, 2, 1, 6, 7]
def baseStart_2969007 : Nat := 118140960795 + 2969007 * 2 ^ 59
def prefixEnd_2969007 : Nat := 4983230072969 + 3 ^ 40 * 2969007 * 2
def baseEnd_2969007 : Nat := 169391961951507831128699

theorem tailTrace_2969007 : CollatzResearch.WordTrace tailWord_2969007 prefixEnd_2969007 169391961951507831128699 := by
  unfold tailWord_2969007
  simp only [CollatzResearch.WordTrace]
  refine ⟨108288581554802179871121275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72192387703201453247414183 108288581554802179871121275)
  ·
    refine ⟨162432872332203269806681913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108288581554802179871121275 162432872332203269806681913)
    ·
      refine ⟨121824654249152452355011435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162432872332203269806681913 121824654249152452355011435)
      ·
        refine ⟨182736981373728678532517153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121824654249152452355011435 182736981373728678532517153)
        ·
          refine ⟨137052736030296508899387865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182736981373728678532517153 137052736030296508899387865)
          ·
            refine ⟨102789552022722381674540899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137052736030296508899387865 102789552022722381674540899)
            ·
              refine ⟨154184328034083572511811349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102789552022722381674540899 154184328034083572511811349)
              ·
                refine ⟨7227390376597667461491157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154184328034083572511811349 7227390376597667461491157)
                ·
                  refine ⟨169391961951507831128699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7227390376597667461491157 169391961951507831128699)
                  ·
                    rfl

theorem cell23_2969007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 6, 7].length) (baseStart_2969007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969007 prefixEnd_2969007 := by exact prefixLift 2969007
  have htrace : WordTrace (prefixWord ++ tailWord_2969007) baseStart_2969007 baseEnd_2969007 := by
    simpa [prefixWord, tailWord_2969007, baseEnd_2969007] using wordTrace_append hprefix tailTrace_2969007
  have hstable : (prefixWord ++ tailWord_2969007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969007).length < 2 ^ (prefixWord ++ tailWord_2969007).sum := by decide
  have hdescent : baseEnd_2969007 < baseStart_2969007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969067 : List Nat := [1, 1, 1, 1, 2, 3, 2, 1, 1, 10]
def baseStart_2969067 : Nat := 118140960795 + 2969067 * 2 ^ 59
def prefixEnd_2969067 : Nat := 4983230072969 + 3 ^ 40 * 2969067 * 2
def baseEnd_2969067 : Nat := 508186155467613415136005

theorem tailTrace_2969067 : CollatzResearch.WordTrace tailWord_2969067 prefixEnd_2969067 508186155467613415136005 := by
  unfold tailWord_2969067
  simp only [CollatzResearch.WordTrace]
  refine ⟨108290769934584810118305455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72193846623056540078870303 108290769934584810118305455)
  ·
    refine ⟨162436154901877215177458183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108290769934584810118305455 162436154901877215177458183)
    ·
      refine ⟨243654232352815822766187275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162436154901877215177458183 243654232352815822766187275)
      ·
        refine ⟨365481348529223734149280913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243654232352815822766187275 365481348529223734149280913)
        ·
          refine ⟨274111011396917800611960685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365481348529223734149280913 274111011396917800611960685)
          ·
            refine ⟨102791629273844175229485257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274111011396917800611960685 102791629273844175229485257)
            ·
              refine ⟨77093721955383131422113943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102791629273844175229485257 77093721955383131422113943)
              ·
                refine ⟨115640582933074697133170915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77093721955383131422113943 115640582933074697133170915)
                ·
                  refine ⟨173460874399612045699756373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 115640582933074697133170915 173460874399612045699756373)
                  ·
                    refine ⟨508186155467613415136005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 173460874399612045699756373 508186155467613415136005)
                    ·
                      rfl

theorem cell23_2969067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 1, 1, 10].length) (baseStart_2969067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969067 prefixEnd_2969067 := by exact prefixLift 2969067
  have htrace : WordTrace (prefixWord ++ tailWord_2969067) baseStart_2969067 baseEnd_2969067 := by
    simpa [prefixWord, tailWord_2969067, baseEnd_2969067] using wordTrace_append hprefix tailTrace_2969067
  have hstable : (prefixWord ++ tailWord_2969067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969067).length < 2 ^ (prefixWord ++ tailWord_2969067).sum := by decide
  have hdescent : baseEnd_2969067 < baseStart_2969067 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969086 : List Nat := [4, 2, 2, 3, 2, 1, 1, 2, 2, 2, 2]
def baseStart_2969086 : Nat := 118140960795 + 2969086 * 2 ^ 59
def prefixEnd_2969086 : Nat := 4983230072969 + 3 ^ 40 * 2969086 * 2
def baseEnd_2969086 : Nat := 1524568222535275671070429

theorem tailTrace_2969086 : CollatzResearch.WordTrace tailWord_2969086 prefixEnd_2969086 1524568222535275671070429 := by
  unfold tailWord_2969086
  simp only [CollatzResearch.WordTrace]
  refine ⟨13536432865189497045405889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72194308614343984242164741 13536432865189497045405889)
  ·
    refine ⟨10152324648892122784054417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13536432865189497045405889 10152324648892122784054417)
    ·
      refine ⟨7614243486669092088040813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10152324648892122784054417 7614243486669092088040813)
      ·
        refine ⟨2855341307500909533015305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7614243486669092088040813 2855341307500909533015305)
        ·
          refine ⟨2141505980625682149761479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855341307500909533015305 2141505980625682149761479)
          ·
            refine ⟨3212258970938523224642219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141505980625682149761479 3212258970938523224642219)
            ·
              refine ⟨4818388456407784836963329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212258970938523224642219 4818388456407784836963329)
              ·
                refine ⟨3613791342305838627722497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4818388456407784836963329 3613791342305838627722497)
                ·
                  refine ⟨2710343506729378970791873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3613791342305838627722497 2710343506729378970791873)
                  ·
                    refine ⟨2032757630047034228093905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2710343506729378970791873 2032757630047034228093905)
                    ·
                      refine ⟨1524568222535275671070429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032757630047034228093905 1524568222535275671070429)
                      ·
                        rfl

theorem cell23_2969086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 2, 2].length) (baseStart_2969086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969086 prefixEnd_2969086 := by exact prefixLift 2969086
  have htrace : WordTrace (prefixWord ++ tailWord_2969086) baseStart_2969086 baseEnd_2969086 := by
    simpa [prefixWord, tailWord_2969086, baseEnd_2969086] using wordTrace_append hprefix tailTrace_2969086
  have hstable : (prefixWord ++ tailWord_2969086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969086).length < 2 ^ (prefixWord ++ tailWord_2969086).sum := by decide
  have hdescent : baseEnd_2969086 < baseStart_2969086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969191 : List Nat := [1, 1, 5, 1, 1, 1, 2, 1, 6, 4]
def baseStart_2969191 : Nat := 118140960795 + 2969191 * 2 ^ 59
def prefixEnd_2969191 : Nat := 4983230072969 + 3 ^ 40 * 2969191 * 2
def baseEnd_2969191 : Nat := 508207379334665920085815

theorem tailTrace_2969191 : CollatzResearch.WordTrace tailWord_2969191 prefixEnd_2969191 508207379334665920085815 := by
  unfold tailWord_2969191
  simp only [CollatzResearch.WordTrace]
  refine ⟨108295292586135579295819427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72196861724090386197212951 108295292586135579295819427)
  ·
    refine ⟨162442938879203368943729141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108295292586135579295819427 162442938879203368943729141)
    ·
      refine ⟨15229025519925315838474607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162442938879203368943729141 15229025519925315838474607)
      ·
        refine ⟨22843538279887973757711911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15229025519925315838474607 22843538279887973757711911)
        ·
          refine ⟨34265307419831960636567867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22843538279887973757711911 34265307419831960636567867)
          ·
            refine ⟨51397961129747940954851801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34265307419831960636567867 51397961129747940954851801)
            ·
              refine ⟨38548470847310955716138851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51397961129747940954851801 38548470847310955716138851)
              ·
                refine ⟨57822706270966433574208277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38548470847310955716138851 57822706270966433574208277)
                ·
                  refine ⟨2710439356451551573791013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57822706270966433574208277 2710439356451551573791013)
                  ·
                    refine ⟨508207379334665920085815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710439356451551573791013 508207379334665920085815)
                    ·
                      rfl

theorem cell23_2969191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_2969191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969191 prefixEnd_2969191 := by exact prefixLift 2969191
  have htrace : WordTrace (prefixWord ++ tailWord_2969191) baseStart_2969191 baseEnd_2969191 := by
    simpa [prefixWord, tailWord_2969191, baseEnd_2969191] using wordTrace_append hprefix tailTrace_2969191
  have hstable : (prefixWord ++ tailWord_2969191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969191).length < 2 ^ (prefixWord ++ tailWord_2969191).sum := by decide
  have hdescent : baseEnd_2969191 < baseStart_2969191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969248 : List Nat := [2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3]
def baseStart_2969248 : Nat := 118140960795 + 2969248 * 2 ^ 59
def prefixEnd_2969248 : Nat := 4983230072969 + 3 ^ 40 * 2969248 * 2
def baseEnd_2969248 : Nat := 1524651406401304037244683

theorem tailTrace_2969248 : CollatzResearch.WordTrace tailWord_2969248 prefixEnd_2969248 1524651406401304037244683 := by
  unfold tailWord_2969248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54148685773464539015322199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72198247697952718687096265 54148685773464539015322199)
  ·
    refine ⟨81223028660196808522983299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54148685773464539015322199 81223028660196808522983299)
    ·
      refine ⟨121834542990295212784474949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81223028660196808522983299 121834542990295212784474949)
      ·
        refine ⟨22843976810680352397089053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121834542990295212784474949 22843976810680352397089053)
        ·
          refine ⟨8566491304005132148908395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22843976810680352397089053 8566491304005132148908395)
          ·
            refine ⟨12849736956007698223362593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566491304005132148908395 12849736956007698223362593)
            ·
              refine ⟨9637302717005773667521945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12849736956007698223362593 9637302717005773667521945)
              ·
                refine ⟨7227977037754330250641459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9637302717005773667521945 7227977037754330250641459)
                ·
                  refine ⟨10841965556631495375962189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7227977037754330250641459 10841965556631495375962189)
                  ·
                    refine ⟨4065737083736810765985821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10841965556631495375962189 4065737083736810765985821)
                    ·
                      refine ⟨1524651406401304037244683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4065737083736810765985821 1524651406401304037244683)
                      ·
                        rfl

theorem cell23_2969248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 2, 2, 1, 3, 3].length) (baseStart_2969248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969248 prefixEnd_2969248 := by exact prefixLift 2969248
  have htrace : WordTrace (prefixWord ++ tailWord_2969248) baseStart_2969248 baseEnd_2969248 := by
    simpa [prefixWord, tailWord_2969248, baseEnd_2969248] using wordTrace_append hprefix tailTrace_2969248
  have hstable : (prefixWord ++ tailWord_2969248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969248).length < 2 ^ (prefixWord ++ tailWord_2969248).sum := by decide
  have hdescent : baseEnd_2969248 < baseStart_2969248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969249 : List Nat := [1, 2, 3, 3, 2, 2, 2, 3, 1, 2, 2]
def baseStart_2969249 : Nat := 118140960795 + 2969249 * 2 ^ 59
def prefixEnd_2969249 : Nat := 4983230072969 + 3 ^ 40 * 2969249 * 2
def baseEnd_2969249 : Nat := 1524651919881958533332179

theorem tailTrace_2969249 : CollatzResearch.WordTrace tailWord_2969249 prefixEnd_2969249 1524651919881958533332179 := by
  unfold tailWord_2969249
  simp only [CollatzResearch.WordTrace]
  refine ⟨108297408019925455201430801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72198272013283636800953867 108297408019925455201430801)
  ·
    refine ⟨81223056014944091401073101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108297408019925455201430801 81223056014944091401073101)
    ·
      refine ⟨30458646005604034275402413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81223056014944091401073101 30458646005604034275402413)
      ·
        refine ⟨11421992252101512853275905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30458646005604034275402413 11421992252101512853275905)
        ·
          refine ⟨8566494189076134639956929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11421992252101512853275905 8566494189076134639956929)
          ·
            refine ⟨6424870641807100979967697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8566494189076134639956929 6424870641807100979967697)
            ·
              refine ⟨4818652981355325734975773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6424870641807100979967697 4818652981355325734975773)
              ·
                refine ⟨1806994868008247150615915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4818652981355325734975773 1806994868008247150615915)
                ·
                  refine ⟨2710492302012370725923873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1806994868008247150615915 2710492302012370725923873)
                  ·
                    refine ⟨2032869226509278044442905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2710492302012370725923873 2032869226509278044442905)
                    ·
                      refine ⟨1524651919881958533332179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032869226509278044442905 1524651919881958533332179)
                      ·
                        rfl

theorem cell23_2969249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 2, 2, 3, 1, 2, 2].length) (baseStart_2969249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969249 prefixEnd_2969249 := by exact prefixLift 2969249
  have htrace : WordTrace (prefixWord ++ tailWord_2969249) baseStart_2969249 baseEnd_2969249 := by
    simpa [prefixWord, tailWord_2969249, baseEnd_2969249] using wordTrace_append hprefix tailTrace_2969249
  have hstable : (prefixWord ++ tailWord_2969249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969249).length < 2 ^ (prefixWord ++ tailWord_2969249).sum := by decide
  have hdescent : baseEnd_2969249 < baseStart_2969249 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969252 : List Nat := [2, 3, 1, 2, 2, 4, 2, 1, 1, 2, 3]
def baseStart_2969252 : Nat := 118140960795 + 2969252 * 2 ^ 59
def prefixEnd_2969252 : Nat := 4983230072969 + 3 ^ 40 * 2969252 * 2
def baseEnd_2969252 : Nat := 1524653460323922021594665

theorem tailTrace_2969252 : CollatzResearch.WordTrace tailWord_2969252 prefixEnd_2969252 1524653460323922021594665 := by
  unfold tailWord_2969252
  simp only [CollatzResearch.WordTrace]
  refine ⟨54148758719457293356895005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72198344959276391142526673 54148758719457293356895005)
  ·
    refine ⟨20305784519796485008835627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54148758719457293356895005 20305784519796485008835627)
    ·
      refine ⟨30458676779694727513253441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20305784519796485008835627 30458676779694727513253441)
      ·
        refine ⟨22844007584771045634940081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30458676779694727513253441 22844007584771045634940081)
        ·
          refine ⟨17133005688578284226205061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22844007584771045634940081 17133005688578284226205061)
          ·
            refine ⟨3212438566608428292413449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17133005688578284226205061 3212438566608428292413449)
            ·
              refine ⟨2409328924956321219310087, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3212438566608428292413449 2409328924956321219310087)
              ·
                refine ⟨3613993387434481828965131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409328924956321219310087 3613993387434481828965131)
                ·
                  refine ⟨5420990081151722743447697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3613993387434481828965131 5420990081151722743447697)
                  ·
                    refine ⟨4065742560863792057585773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5420990081151722743447697 4065742560863792057585773)
                    ·
                      refine ⟨1524653460323922021594665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4065742560863792057585773 1524653460323922021594665)
                      ·
                        rfl

theorem cell23_2969252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 4, 2, 1, 1, 2, 3].length) (baseStart_2969252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969252 prefixEnd_2969252 := by exact prefixLift 2969252
  have htrace : WordTrace (prefixWord ++ tailWord_2969252) baseStart_2969252 baseEnd_2969252 := by
    simpa [prefixWord, tailWord_2969252, baseEnd_2969252] using wordTrace_append hprefix tailTrace_2969252
  have hstable : (prefixWord ++ tailWord_2969252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969252).length < 2 ^ (prefixWord ++ tailWord_2969252).sum := by decide
  have hdescent : baseEnd_2969252 < baseStart_2969252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969291 : List Nat := [1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3]
def baseStart_2969291 : Nat := 118140960795 + 2969291 * 2 ^ 59
def prefixEnd_2969291 : Nat := 4983230072969 + 3 ^ 40 * 2969291 * 2
def baseEnd_2969291 : Nat := 1524673486069447369006985

theorem tailTrace_2969291 : CollatzResearch.WordTrace tailWord_2969291 prefixEnd_2969291 1524673486069447369006985 := by
  unfold tailWord_2969291
  simp only [CollatzResearch.WordTrace]
  refine ⟨108298939885773296374459727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72199293257182197582973151 108298939885773296374459727)
  ·
    refine ⟨162448409828659944561689591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108298939885773296374459727 162448409828659944561689591)
    ·
      refine ⟨243672614742989916842534387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162448409828659944561689591 243672614742989916842534387)
      ·
        refine ⟨365508922114484875263801581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243672614742989916842534387 365508922114484875263801581)
        ·
          refine ⟨137065845792931828223925593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365508922114484875263801581 137065845792931828223925593)
          ·
            refine ⟨102799384344698871167944195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137065845792931828223925593 102799384344698871167944195)
            ·
              refine ⟨154199076517048306751916293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102799384344698871167944195 154199076517048306751916293)
              ·
                refine ⟨28912326846946557515984305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154199076517048306751916293 28912326846946557515984305)
                ·
                  refine ⟨21684245135209918136988229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28912326846946557515984305 21684245135209918136988229)
                  ·
                    refine ⟨4065795962851859650685293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21684245135209918136988229 4065795962851859650685293)
                    ·
                      refine ⟨1524673486069447369006985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4065795962851859650685293 1524673486069447369006985)
                      ·
                        rfl

theorem cell23_2969291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 3].length) (baseStart_2969291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969291 prefixEnd_2969291 := by exact prefixLift 2969291
  have htrace : WordTrace (prefixWord ++ tailWord_2969291) baseStart_2969291 baseEnd_2969291 := by
    simpa [prefixWord, tailWord_2969291, baseEnd_2969291] using wordTrace_append hprefix tailTrace_2969291
  have hstable : (prefixWord ++ tailWord_2969291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969291).length < 2 ^ (prefixWord ++ tailWord_2969291).sum := by decide
  have hdescent : baseEnd_2969291 < baseStart_2969291 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969305 : List Nat := [1, 2, 1, 2, 3, 3, 1, 2, 4, 2, 2]
def baseStart_2969305 : Nat := 118140960795 + 2969305 * 2 ^ 59
def prefixEnd_2969305 : Nat := 4983230072969 + 3 ^ 40 * 2969305 * 2
def baseEnd_2969305 : Nat := 1524680674798610314231921

theorem tailTrace_2969305 : CollatzResearch.WordTrace tailWord_2969305 prefixEnd_2969305 1524680674798610314231921 := by
  unfold tailWord_2969305
  simp only [CollatzResearch.WordTrace]
  refine ⟨108299450507722576765469369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72199633671815051176979579 108299450507722576765469369)
  ·
    refine ⟨81224587880791932574102027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108299450507722576765469369 81224587880791932574102027)
    ·
      refine ⟨121836881821187898861153041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81224587880791932574102027 121836881821187898861153041)
      ·
        refine ⟨91377661365890924145864781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121836881821187898861153041 91377661365890924145864781)
        ·
          refine ⟨34266623012209096554699293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91377661365890924145864781 34266623012209096554699293)
          ·
            refine ⟨12849983629578411208012235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34266623012209096554699293 12849983629578411208012235)
            ·
              refine ⟨19274975444367616812018353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12849983629578411208012235 19274975444367616812018353)
              ·
                refine ⟨14456231583275712609013765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19274975444367616812018353 14456231583275712609013765)
                ·
                  refine ⟨2710543421864196114190081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14456231583275712609013765 2710543421864196114190081)
                  ·
                    refine ⟨2032907566398147085642561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2710543421864196114190081 2032907566398147085642561)
                    ·
                      refine ⟨1524680674798610314231921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2032907566398147085642561 1524680674798610314231921)
                      ·
                        rfl

theorem cell23_2969305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 2, 2].length) (baseStart_2969305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969305 prefixEnd_2969305 := by exact prefixLift 2969305
  have htrace : WordTrace (prefixWord ++ tailWord_2969305) baseStart_2969305 baseEnd_2969305 := by
    simpa [prefixWord, tailWord_2969305, baseEnd_2969305] using wordTrace_append hprefix tailTrace_2969305
  have hstable : (prefixWord ++ tailWord_2969305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969305).length < 2 ^ (prefixWord ++ tailWord_2969305).sum := by decide
  have hdescent : baseEnd_2969305 < baseStart_2969305 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969341 : List Nat := [1, 4, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_2969341 : Nat := 118140960795 + 2969341 * 2 ^ 59
def prefixEnd_2969341 : Nat := 4983230072969 + 3 ^ 40 * 2969341 * 2
def baseEnd_2969341 : Nat := 508233053367390724460585

theorem tailTrace_2969341 : CollatzResearch.WordTrace tailWord_2969341 prefixEnd_2969341 508233053367390724460585 := by
  unfold tailWord_2969341
  simp only [CollatzResearch.WordTrace]
  refine ⟨108300763535592154913779877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72200509023728103275853251 108300763535592154913779877)
  ·
    refine ⟨20306393162923529046333727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108300763535592154913779877 20306393162923529046333727)
    ·
      refine ⟨30459589744385293569500591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306393162923529046333727 30459589744385293569500591)
      ·
        refine ⟨45689384616577940354250887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30459589744385293569500591 45689384616577940354250887)
        ·
          refine ⟨68534076924866910531376331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45689384616577940354250887 68534076924866910531376331)
          ·
            refine ⟨102801115387300365797064497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68534076924866910531376331 102801115387300365797064497)
            ·
              refine ⟨77100836540475274347798373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102801115387300365797064497 77100836540475274347798373)
              ·
                refine ⟨14456406851339113940212195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77100836540475274347798373 14456406851339113940212195)
                ·
                  refine ⟨21684610277008670910318293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14456406851339113940212195 21684610277008670910318293)
                  ·
                    refine ⟨508233053367390724460585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21684610277008670910318293 508233053367390724460585)
                    ·
                      rfl

theorem cell23_2969341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_2969341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969341 prefixEnd_2969341 := by exact prefixLift 2969341
  have htrace : WordTrace (prefixWord ++ tailWord_2969341) baseStart_2969341 baseEnd_2969341 := by
    simpa [prefixWord, tailWord_2969341, baseEnd_2969341] using wordTrace_append hprefix tailTrace_2969341
  have hstable : (prefixWord ++ tailWord_2969341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969341).length < 2 ^ (prefixWord ++ tailWord_2969341).sum := by decide
  have hdescent : baseEnd_2969341 < baseStart_2969341 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969358 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 2, 5]
def baseStart_2969358 : Nat := 118140960795 + 2969358 * 2 ^ 59
def prefixEnd_2969358 : Nat := 4983230072969 + 3 ^ 40 * 2969358 * 2
def baseEnd_2969358 : Nat := 508235963091099535623059

theorem tailTrace_2969358 : CollatzResearch.WordTrace tailWord_2969358 prefixEnd_2969358 508235963091099535623059 := by
  unfold tailWord_2969358
  simp only [CollatzResearch.WordTrace]
  refine ⟨13537672947066320852143591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72200922384353711211432485 13537672947066320852143591)
  ·
    refine ⟨20306509420599481278215387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13537672947066320852143591 20306509420599481278215387)
    ·
      refine ⟨30459764130899221917323081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306509420599481278215387 30459764130899221917323081)
      ·
        refine ⟨22844823098174416437992311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30459764130899221917323081 22844823098174416437992311)
        ·
          refine ⟨34267234647261624656988467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22844823098174416437992311 34267234647261624656988467)
          ·
            refine ⟨51400851970892436985482701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34267234647261624656988467 51400851970892436985482701)
            ·
              refine ⟨19275319489084663869556013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51400851970892436985482701 19275319489084663869556013)
              ·
                refine ⟨7228244808406748951083505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19275319489084663869556013 7228244808406748951083505)
                ·
                  refine ⟨5421183606305061713312629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7228244808406748951083505 5421183606305061713312629)
                  ·
                    refine ⟨508235963091099535623059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5421183606305061713312629 508235963091099535623059)
                    ·
                      rfl

theorem cell23_2969358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 2, 5].length) (baseStart_2969358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969358 prefixEnd_2969358 := by exact prefixLift 2969358
  have htrace : WordTrace (prefixWord ++ tailWord_2969358) baseStart_2969358 baseEnd_2969358 := by
    simpa [prefixWord, tailWord_2969358, baseEnd_2969358] using wordTrace_append hprefix tailTrace_2969358
  have hstable : (prefixWord ++ tailWord_2969358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969358).length < 2 ^ (prefixWord ++ tailWord_2969358).sum := by decide
  have hdescent : baseEnd_2969358 < baseStart_2969358 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969391 : List Nat := [1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6]
def baseStart_2969391 : Nat := 118140960795 + 2969391 * 2 ^ 59
def prefixEnd_2969391 : Nat := 4983230072969 + 3 ^ 40 * 2969391 * 2
def baseEnd_2969391 : Nat := 1524724834134896977756525

theorem tailTrace_2969391 : CollatzResearch.WordTrace tailWord_2969391 prefixEnd_2969391 1524724834134896977756525 := by
  unfold tailWord_2969391
  simp only [CollatzResearch.WordTrace]
  refine ⟨108302587185411013453100027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72201724790274008968733351 108302587185411013453100027)
  ·
    refine ⟨162453880778116520179650041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108302587185411013453100027 162453880778116520179650041)
    ·
      refine ⟨121840410583587390134737531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162453880778116520179650041 121840410583587390134737531)
      ·
        refine ⟨182760615875381085202106297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121840410583587390134737531 182760615875381085202106297)
        ·
          refine ⟨137070461906535813901579723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182760615875381085202106297 137070461906535813901579723)
          ·
            refine ⟨205605692859803720852369585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137070461906535813901579723 205605692859803720852369585)
            ·
              refine ⟨154204269644852790639277189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 205605692859803720852369585 154204269644852790639277189)
              ·
                refine ⟨28913300558409898244864473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154204269644852790639277189 28913300558409898244864473)
                ·
                  refine ⟨21684975418807423683648355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28913300558409898244864473 21684975418807423683648355)
                  ·
                    refine ⟨32527463128211135525472533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21684975418807423683648355 32527463128211135525472533)
                    ·
                      refine ⟨1524724834134896977756525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32527463128211135525472533 1524724834134896977756525)
                      ·
                        rfl

theorem cell23_2969391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 6].length) (baseStart_2969391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969391 prefixEnd_2969391 := by exact prefixLift 2969391
  have htrace : WordTrace (prefixWord ++ tailWord_2969391) baseStart_2969391 baseEnd_2969391 := by
    simpa [prefixWord, tailWord_2969391, baseEnd_2969391] using wordTrace_append hprefix tailTrace_2969391
  have hstable : (prefixWord ++ tailWord_2969391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969391).length < 2 ^ (prefixWord ++ tailWord_2969391).sum := by decide
  have hdescent : baseEnd_2969391 < baseStart_2969391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969405 : List Nat := [1, 4, 1, 4, 1, 1, 1, 1, 5, 4]
def baseStart_2969405 : Nat := 118140960795 + 2969405 * 2 ^ 59
def prefixEnd_2969405 : Nat := 4983230072969 + 3 ^ 40 * 2969405 * 2
def baseEnd_2969405 : Nat := 508244007621353307660487

theorem tailTrace_2969405 : CollatzResearch.WordTrace tailWord_2969405 prefixEnd_2969405 508244007621353307660487 := by
  unfold tailWord_2969405
  simp only [CollatzResearch.WordTrace]
  refine ⟨108303097807360293844109669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72202065204906862562739779 108303097807360293844109669)
  ·
    refine ⟨20306830838880055095770563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108303097807360293844109669 20306830838880055095770563)
    ·
      refine ⟨30460246258320082643655845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20306830838880055095770563 30460246258320082643655845)
      ·
        refine ⟨5711296173435015495685471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30460246258320082643655845 5711296173435015495685471)
        ·
          refine ⟨8566944260152523243528207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5711296173435015495685471 8566944260152523243528207)
          ·
            refine ⟨12850416390228784865292311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8566944260152523243528207 12850416390228784865292311)
            ·
              refine ⟨19275624585343177297938467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850416390228784865292311 19275624585343177297938467)
              ·
                refine ⟨28913436878014765946907701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19275624585343177297938467 28913436878014765946907701)
                ·
                  refine ⟨2710634707313884307522597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28913436878014765946907701 2710634707313884307522597)
                  ·
                    refine ⟨508244007621353307660487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710634707313884307522597 508244007621353307660487)
                    ·
                      rfl

theorem cell23_2969405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 4].length) (baseStart_2969405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969405 prefixEnd_2969405 := by exact prefixLift 2969405
  have htrace : WordTrace (prefixWord ++ tailWord_2969405) baseStart_2969405 baseEnd_2969405 := by
    simpa [prefixWord, tailWord_2969405, baseEnd_2969405] using wordTrace_append hprefix tailTrace_2969405
  have hstable : (prefixWord ++ tailWord_2969405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969405).length < 2 ^ (prefixWord ++ tailWord_2969405).sum := by decide
  have hdescent : baseEnd_2969405 < baseStart_2969405 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969415 : List Nat := [1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3]
def baseStart_2969415 : Nat := 118140960795 + 2969415 * 2 ^ 59
def prefixEnd_2969415 : Nat := 4983230072969 + 3 ^ 40 * 2969415 * 2
def baseEnd_2969415 : Nat := 1524737157670604883856415

theorem tailTrace_2969415 : CollatzResearch.WordTrace tailWord_2969415 prefixEnd_2969415 1524737157670604883856415 := by
  unfold tailWord_2969415
  simp only [CollatzResearch.WordTrace]
  refine ⟨108303462537324065551973699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72202308358216043701315799 108303462537324065551973699)
  ·
    refine ⟨162455193805986098327960549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108303462537324065551973699 162455193805986098327960549)
    ·
      refine ⟨30460348838622393436492603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162455193805986098327960549 30460348838622393436492603)
      ·
        refine ⟨45690523257933590154738905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30460348838622393436492603 45690523257933590154738905)
        ·
          refine ⟨34267892443450192616054179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45690523257933590154738905 34267892443450192616054179)
          ·
            refine ⟨51401838665175288924081269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34267892443450192616054179 51401838665175288924081269)
            ·
              refine ⟨4818922374860183336632619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51401838665175288924081269 4818922374860183336632619)
              ·
                refine ⟨7228383562290275004948929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4818922374860183336632619 7228383562290275004948929)
                ·
                  refine ⟨5421287671717706253711697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7228383562290275004948929 5421287671717706253711697)
                  ·
                    refine ⟨4065965753788279690283773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5421287671717706253711697 4065965753788279690283773)
                    ·
                      refine ⟨1524737157670604883856415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4065965753788279690283773 1524737157670604883856415)
                      ·
                        rfl

theorem cell23_2969415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 5, 1, 2, 2, 3].length) (baseStart_2969415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969415 prefixEnd_2969415 := by exact prefixLift 2969415
  have htrace : WordTrace (prefixWord ++ tailWord_2969415) baseStart_2969415 baseEnd_2969415 := by
    simpa [prefixWord, tailWord_2969415, baseEnd_2969415] using wordTrace_append hprefix tailTrace_2969415
  have hstable : (prefixWord ++ tailWord_2969415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969415).length < 2 ^ (prefixWord ++ tailWord_2969415).sum := by decide
  have hdescent : baseEnd_2969415 < baseStart_2969415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969465 : List Nat := [1, 2, 1, 3, 2, 2, 4, 2, 1, 5]
def baseStart_2969465 : Nat := 118140960795 + 2969465 * 2 ^ 59
def prefixEnd_2969465 : Nat := 4983230072969 + 3 ^ 40 * 2969465 * 2
def baseEnd_2969465 : Nat := 508254277234443229410395

theorem tailTrace_2969465 : CollatzResearch.WordTrace tailWord_2969465 prefixEnd_2969465 508254277234443229410395 := by
  unfold tailWord_2969465
  simp only [CollatzResearch.WordTrace]
  refine ⟨108305286187142924091293849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72203524124761949394195899 108305286187142924091293849)
  ·
    refine ⟨81228964640357193068470387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108305286187142924091293849 81228964640357193068470387)
    ·
      refine ⟨121843446960535789602705581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81228964640357193068470387 121843446960535789602705581)
      ·
        refine ⟨45691292610200921101014593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121843446960535789602705581 45691292610200921101014593)
        ·
          refine ⟨34268469457650690825760945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45691292610200921101014593 34268469457650690825760945)
          ·
            refine ⟨25701352093238018119320709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34268469457650690825760945 25701352093238018119320709)
            ·
              refine ⟨4819003517482128397372633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25701352093238018119320709 4819003517482128397372633)
              ·
                refine ⟨3614252638111596298029475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819003517482128397372633 3614252638111596298029475)
                ·
                  refine ⟨5421378957167394447044213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614252638111596298029475 5421378957167394447044213)
                  ·
                    refine ⟨508254277234443229410395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5421378957167394447044213 508254277234443229410395)
                    ·
                      rfl

theorem cell23_2969465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 5].length) (baseStart_2969465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969465 prefixEnd_2969465 := by exact prefixLift 2969465
  have htrace : WordTrace (prefixWord ++ tailWord_2969465) baseStart_2969465 baseEnd_2969465 := by
    simpa [prefixWord, tailWord_2969465, baseEnd_2969465] using wordTrace_append hprefix tailTrace_2969465
  have hstable : (prefixWord ++ tailWord_2969465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969465).length < 2 ^ (prefixWord ++ tailWord_2969465).sum := by decide
  have hdescent : baseEnd_2969465 < baseStart_2969465 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969473 : List Nat := [1, 2, 4, 4, 2, 1, 1, 3, 1, 4]
def baseStart_2969473 : Nat := 118140960795 + 2969473 * 2 ^ 59
def prefixEnd_2969473 : Nat := 4983230072969 + 3 ^ 40 * 2969473 * 2
def baseEnd_2969473 : Nat := 508255646516188552310383

theorem tailTrace_2969473 : CollatzResearch.WordTrace tailWord_2969473 prefixEnd_2969473 508255646516188552310383 := by
  unfold tailWord_2969473
  simp only [CollatzResearch.WordTrace]
  refine ⟨108305577971113941457585073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72203718647409294305056715 108305577971113941457585073)
  ·
    refine ⟨81229183478335456093188805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108305577971113941457585073 81229183478335456093188805)
    ·
      refine ⟨15230471902187898017472901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81229183478335456093188805 15230471902187898017472901)
      ·
        refine ⟨2855713481660230878276169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 15230471902187898017472901 2855713481660230878276169)
        ·
          refine ⟨2141785111245173158707127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2855713481660230878276169 2141785111245173158707127)
          ·
            refine ⟨3212677666867759738060691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2141785111245173158707127 3212677666867759738060691)
            ·
              refine ⟨4819016500301639607091037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212677666867759738060691 4819016500301639607091037)
              ·
                refine ⟨1807131187613114852659139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4819016500301639607091037 1807131187613114852659139)
                ·
                  refine ⟨2710696781419672278988709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1807131187613114852659139 2710696781419672278988709)
                  ·
                    refine ⟨508255646516188552310383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710696781419672278988709 508255646516188552310383)
                    ·
                      rfl

theorem cell23_2969473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_2969473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969473 prefixEnd_2969473 := by exact prefixLift 2969473
  have htrace : WordTrace (prefixWord ++ tailWord_2969473) baseStart_2969473 baseEnd_2969473 := by
    simpa [prefixWord, tailWord_2969473, baseEnd_2969473] using wordTrace_append hprefix tailTrace_2969473
  have hstable : (prefixWord ++ tailWord_2969473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969473).length < 2 ^ (prefixWord ++ tailWord_2969473).sum := by decide
  have hdescent : baseEnd_2969473 < baseStart_2969473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969488 : List Nat := [2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5]
def baseStart_2969488 : Nat := 118140960795 + 2969488 * 2 ^ 59
def prefixEnd_2969488 : Nat := 4983230072969 + 3 ^ 40 * 2969488 * 2
def baseEnd_2969488 : Nat := 1524774641758383098243579

theorem tailTrace_2969488 : CollatzResearch.WordTrace tailWord_2969488 prefixEnd_2969488 1524774641758383098243579 := by
  unfold tailWord_2969488
  simp only [CollatzResearch.WordTrace]
  refine ⟨54153062533029799509690559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72204083377373066012920745 54153062533029799509690559)
  ·
    refine ⟨81229593799544699264535839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54153062533029799509690559 81229593799544699264535839)
    ·
      refine ⟨121844390699317048896803759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81229593799544699264535839 121844390699317048896803759)
      ·
        refine ⟨182766586048975573345205639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121844390699317048896803759 182766586048975573345205639)
        ·
          refine ⟨274149879073463360017808459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182766586048975573345205639 274149879073463360017808459)
          ·
            refine ⟨411224818610195040026712689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274149879073463360017808459 411224818610195040026712689)
            ·
              refine ⟨308418613957646280020034517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411224818610195040026712689 308418613957646280020034517)
              ·
                refine ⟨7228561264632334687969559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 308418613957646280020034517 7228561264632334687969559)
                ·
                  refine ⟨10842841896948502031954339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228561264632334687969559 10842841896948502031954339)
                  ·
                    refine ⟨16264262845422753047931509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10842841896948502031954339 16264262845422753047931509)
                    ·
                      refine ⟨1524774641758383098243579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16264262845422753047931509 1524774641758383098243579)
                      ·
                        rfl

theorem cell23_2969488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 5].length) (baseStart_2969488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969488 prefixEnd_2969488 := by exact prefixLift 2969488
  have htrace : WordTrace (prefixWord ++ tailWord_2969488) baseStart_2969488 baseEnd_2969488 := by
    simpa [prefixWord, tailWord_2969488, baseEnd_2969488] using wordTrace_append hprefix tailTrace_2969488
  have hstable : (prefixWord ++ tailWord_2969488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969488).length < 2 ^ (prefixWord ++ tailWord_2969488).sum := by decide
  have hdescent : baseEnd_2969488 < baseStart_2969488 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969495 : List Nat := [1, 1, 3, 3, 1, 3, 2, 1, 4, 4]
def baseStart_2969495 : Nat := 118140960795 + 2969495 * 2 ^ 59
def prefixEnd_2969495 : Nat := 4983230072969 + 3 ^ 40 * 2969495 * 2
def baseEnd_2969495 : Nat := 508259412040988190285349

theorem tailTrace_2969495 : CollatzResearch.WordTrace tailWord_2969495 prefixEnd_2969495 508259412040988190285349 := by
  unfold tailWord_2969495
  simp only [CollatzResearch.WordTrace]
  refine ⟨108306380377034239214885939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72204253584689492809923959 108306380377034239214885939)
  ·
    refine ⟨162459570565551358822328909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108306380377034239214885939 162459570565551358822328909)
    ·
      refine ⟨60922338962081759558373341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162459570565551358822328909 60922338962081759558373341)
      ·
        refine ⟨22845877110780659834390003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60922338962081759558373341 22845877110780659834390003)
        ·
          refine ⟨34268815666170989751585005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22845877110780659834390003 34268815666170989751585005)
          ·
            refine ⟨12850805874814121156844377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34268815666170989751585005 12850805874814121156844377)
            ·
              refine ⟨9638104406110590867633283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12850805874814121156844377 9638104406110590867633283)
              ·
                refine ⟨14457156609165886301449925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9638104406110590867633283 14457156609165886301449925)
                ·
                  refine ⟨2710716864218603681521861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14457156609165886301449925 2710716864218603681521861)
                  ·
                    refine ⟨508259412040988190285349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2710716864218603681521861 508259412040988190285349)
                    ·
                      rfl

theorem cell23_2969495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 4, 4].length) (baseStart_2969495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969495 prefixEnd_2969495 := by exact prefixLift 2969495
  have htrace : WordTrace (prefixWord ++ tailWord_2969495) baseStart_2969495 baseEnd_2969495 := by
    simpa [prefixWord, tailWord_2969495, baseEnd_2969495] using wordTrace_append hprefix tailTrace_2969495
  have hstable : (prefixWord ++ tailWord_2969495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969495).length < 2 ^ (prefixWord ++ tailWord_2969495).sum := by decide
  have hdescent : baseEnd_2969495 < baseStart_2969495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969496 : List Nat := [2, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3]
def baseStart_2969496 : Nat := 118140960795 + 2969496 * 2 ^ 59
def prefixEnd_2969496 : Nat := 4983230072969 + 3 ^ 40 * 2969496 * 2
def baseEnd_2969496 : Nat := 1524778749603619066943543

theorem tailTrace_2969496 : CollatzResearch.WordTrace tailWord_2969496 prefixEnd_2969496 1524778749603619066943543 := by
  unfold tailWord_2969496
  simp only [CollatzResearch.WordTrace]
  refine ⟨54153208425015308192836171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72204277900020410923781561 54153208425015308192836171)
  ·
    refine ⟨81229812637522962289254257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54153208425015308192836171 81229812637522962289254257)
    ·
      refine ⟨60922359478142221716940693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81229812637522962289254257 60922359478142221716940693)
      ·
        refine ⟨2855735600537916642981595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 60922359478142221716940693 2855735600537916642981595)
        ·
          refine ⟨4283603400806874964472393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855735600537916642981595 4283603400806874964472393)
          ·
            refine ⟨3212702550605156223354295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4283603400806874964472393 3212702550605156223354295)
            ·
              refine ⟨4819053825907734335031443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212702550605156223354295 4819053825907734335031443)
              ·
                refine ⟨7228580738861601502547165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819053825907734335031443 7228580738861601502547165)
                ·
                  refine ⟨2710717777073100563455187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7228580738861601502547165 2710717777073100563455187)
                  ·
                    refine ⟨4066076665609650845182781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2710717777073100563455187 4066076665609650845182781)
                    ·
                      refine ⟨1524778749603619066943543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066076665609650845182781 1524778749603619066943543)
                      ·
                        rfl

theorem cell23_2969496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 2, 1, 1, 3, 1, 3].length) (baseStart_2969496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969496 prefixEnd_2969496 := by exact prefixLift 2969496
  have htrace : WordTrace (prefixWord ++ tailWord_2969496) baseStart_2969496 baseEnd_2969496 := by
    simpa [prefixWord, tailWord_2969496, baseEnd_2969496] using wordTrace_append hprefix tailTrace_2969496
  have hstable : (prefixWord ++ tailWord_2969496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969496).length < 2 ^ (prefixWord ++ tailWord_2969496).sum := by decide
  have hdescent : baseEnd_2969496 < baseStart_2969496 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969508 : List Nat := [2, 3, 1, 2, 1, 3, 1, 10]
def baseStart_2969508 : Nat := 118140960795 + 2969508 * 2 ^ 59
def prefixEnd_2969508 : Nat := 4983230072969 + 3 ^ 40 * 2969508 * 2
def baseEnd_2969508 : Nat := 56473515235980482221981

theorem tailTrace_2969508 : CollatzResearch.WordTrace tailWord_2969508 prefixEnd_2969508 56473515235980482221981 := by
  unfold tailWord_2969508
  simp only [CollatzResearch.WordTrace]
  refine ⟨54153427262993571217554589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72204569683991428290072785 54153427262993571217554589)
  ·
    refine ⟨20307535223622589206582971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54153427262993571217554589 20307535223622589206582971)
    ·
      refine ⟨30461302835433883809874457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20307535223622589206582971 30461302835433883809874457)
      ·
        refine ⟨22845977126575412857405843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30461302835433883809874457 22845977126575412857405843)
        ·
          refine ⟨34268965689863119286108765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22845977126575412857405843 34268965689863119286108765)
          ·
            refine ⟨12850862133698669732290787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34268965689863119286108765 12850862133698669732290787)
            ·
              refine ⟨19276293200548004598436181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12850862133698669732290787 19276293200548004598436181)
              ·
                refine ⟨56473515235980482221981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19276293200548004598436181 56473515235980482221981)
                ·
                  rfl

theorem cell23_2969508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 10].length) (baseStart_2969508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969508 prefixEnd_2969508 := by exact prefixLift 2969508
  have htrace : WordTrace (prefixWord ++ tailWord_2969508) baseStart_2969508 baseEnd_2969508 := by
    simpa [prefixWord, tailWord_2969508, baseEnd_2969508] using wordTrace_append hprefix tailTrace_2969508
  have hstable : (prefixWord ++ tailWord_2969508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969508).length < 2 ^ (prefixWord ++ tailWord_2969508).sum := by decide
  have hdescent : baseEnd_2969508 < baseStart_2969508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969535 : List Nat := [1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3]
def baseStart_2969535 : Nat := 118140960795 + 2969535 * 2 ^ 59
def prefixEnd_2969535 : Nat := 4983230072969 + 3 ^ 40 * 2969535 * 2
def baseEnd_2969535 : Nat := 1524798775349144414355863

theorem tailTrace_2969535 : CollatzResearch.WordTrace tailWord_2969535 prefixEnd_2969535 1524798775349144414355863 := by
  unfold tailWord_2969535
  simp only [CollatzResearch.WordTrace]
  refine ⟨108307839296889326046342059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72205226197926217364228039 108307839296889326046342059)
  ·
    refine ⟨162461758945333989069513089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108307839296889326046342059 162461758945333989069513089)
    ·
      refine ⟨121846319209000491802134817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162461758945333989069513089 121846319209000491802134817)
      ·
        refine ⟨91384739406750368851601113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121846319209000491802134817 91384739406750368851601113)
        ·
          refine ⟨68538554555062776638700835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91384739406750368851601113 68538554555062776638700835)
          ·
            refine ⟨102807831832594164958051253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68538554555062776638700835 102807831832594164958051253)
            ·
              refine ⟨9638234234305702964817305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102807831832594164958051253 9638234234305702964817305)
              ·
                refine ⟨7228675675729277223612979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9638234234305702964817305 7228675675729277223612979)
                ·
                  refine ⟨10843013513593915835419469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228675675729277223612979 10843013513593915835419469)
                  ·
                    refine ⟨4066130067597718438282301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10843013513593915835419469 4066130067597718438282301)
                    ·
                      refine ⟨1524798775349144414355863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066130067597718438282301 1524798775349144414355863)
                      ·
                        rfl

theorem cell23_2969535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 5, 2, 1, 3, 3].length) (baseStart_2969535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969535 prefixEnd_2969535 := by exact prefixLift 2969535
  have htrace : WordTrace (prefixWord ++ tailWord_2969535) baseStart_2969535 baseEnd_2969535 := by
    simpa [prefixWord, tailWord_2969535, baseEnd_2969535] using wordTrace_append hprefix tailTrace_2969535
  have hstable : (prefixWord ++ tailWord_2969535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969535).length < 2 ^ (prefixWord ++ tailWord_2969535).sum := by decide
  have hdescent : baseEnd_2969535 < baseStart_2969535 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969542 : List Nat := [6, 1, 3, 13]
def baseStart_2969542 : Nat := 118140960795 + 2969542 * 2 ^ 59
def prefixEnd_2969542 : Nat := 4983230072969 + 3 ^ 40 * 2969542 * 2
def baseEnd_2969542 : Nat := 697211874583322307713

theorem tailTrace_2969542 : CollatzResearch.WordTrace tailWord_2969542 prefixEnd_2969542 697211874583322307713 := by
  unfold tailWord_2969542
  simp only [CollatzResearch.WordTrace]
  refine ⟨3384627956495748945057715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72205396405242644161231253 3384627956495748945057715)
  ·
    refine ⟨5076941934743623417586573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3384627956495748945057715 5076941934743623417586573)
    ·
      refine ⟨1903853225528858781594965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5076941934743623417586573 1903853225528858781594965)
      ·
        refine ⟨697211874583322307713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 1903853225528858781594965 697211874583322307713)
        ·
          rfl

theorem cell23_2969542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 13].length) (baseStart_2969542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969542 prefixEnd_2969542 := by exact prefixLift 2969542
  have htrace : WordTrace (prefixWord ++ tailWord_2969542) baseStart_2969542 baseEnd_2969542 := by
    simpa [prefixWord, tailWord_2969542, baseEnd_2969542] using wordTrace_append hprefix tailTrace_2969542
  have hstable : (prefixWord ++ tailWord_2969542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969542).length < 2 ^ (prefixWord ++ tailWord_2969542).sum := by decide
  have hdescent : baseEnd_2969542 < baseStart_2969542 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969552 : List Nat := [2, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3]
def baseStart_2969552 : Nat := 118140960795 + 2969552 * 2 ^ 59
def prefixEnd_2969552 : Nat := 4983230072969 + 3 ^ 40 * 2969552 * 2
def baseEnd_2969552 : Nat := 1524807504520270847843285

theorem tailTrace_2969552 : CollatzResearch.WordTrace tailWord_2969552 prefixEnd_2969552 1524807504520270847843285 := by
  unfold tailWord_2969552
  simp only [CollatzResearch.WordTrace]
  refine ⟨54154229668913868974855455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72205639558551825299807273 54154229668913868974855455)
  ·
    refine ⟨81231344503370803462283183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54154229668913868974855455 81231344503370803462283183)
    ·
      refine ⟨121847016755056205193424775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81231344503370803462283183 121847016755056205193424775)
      ·
        refine ⟨182770525132584307790137163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121847016755056205193424775 182770525132584307790137163)
        ·
          refine ⟨274155787698876461685205745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182770525132584307790137163 274155787698876461685205745)
          ·
            refine ⟨205616840774157346263904309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274155787698876461685205745 205616840774157346263904309)
            ·
              refine ⟨19276578822577251212241029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205616840774157346263904309 19276578822577251212241029)
              ·
                refine ⟨3614358529233234602295193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19276578822577251212241029 3614358529233234602295193)
                ·
                  refine ⟨2710768896924925951721395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3614358529233234602295193 2710768896924925951721395)
                  ·
                    refine ⟨4066153345387388927582093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2710768896924925951721395 4066153345387388927582093)
                    ·
                      refine ⟨1524807504520270847843285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066153345387388927582093 1524807504520270847843285)
                      ·
                        rfl

theorem cell23_2969552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 4, 2, 1, 3].length) (baseStart_2969552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969552 prefixEnd_2969552 := by exact prefixLift 2969552
  have htrace : WordTrace (prefixWord ++ tailWord_2969552) baseStart_2969552 baseEnd_2969552 := by
    simpa [prefixWord, tailWord_2969552, baseEnd_2969552] using wordTrace_append hprefix tailTrace_2969552
  have hstable : (prefixWord ++ tailWord_2969552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969552).length < 2 ^ (prefixWord ++ tailWord_2969552).sum := by decide
  have hdescent : baseEnd_2969552 < baseStart_2969552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969592 : List Nat := [2, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2]
def baseStart_2969592 : Nat := 118140960795 + 2969592 * 2 ^ 59
def prefixEnd_2969592 : Nat := 4983230072969 + 3 ^ 40 * 2969592 * 2
def baseEnd_2969592 : Nat := 1524828043746450691343101

theorem tailTrace_2969592 : CollatzResearch.WordTrace tailWord_2969592 prefixEnd_2969592 1524828043746450691343101 := by
  unfold tailWord_2969592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54154959128841412390583515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72206612171788549854111353 54154959128841412390583515)
  ·
    refine ⟨81232438693262118585875273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54154959128841412390583515 81232438693262118585875273)
    ·
      refine ⟨60924329019946588939406455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81232438693262118585875273 60924329019946588939406455)
      ·
        refine ⟨91386493529919883409109683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60924329019946588939406455 91386493529919883409109683)
        ·
          refine ⟨137079740294879825113664525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91386493529919883409109683 137079740294879825113664525)
          ·
            refine ⟨51404902610579934417624197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 137079740294879825113664525 51404902610579934417624197)
            ·
              refine ⟨9638419239483737703304537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51404902610579934417624197 9638419239483737703304537)
              ·
                refine ⟨7228814429612803277478403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9638419239483737703304537 7228814429612803277478403)
                ·
                  refine ⟨10843221644419204916217605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7228814429612803277478403 10843221644419204916217605)
                  ·
                    refine ⟨2033104058328600921790801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10843221644419204916217605 2033104058328600921790801)
                    ·
                      refine ⟨1524828043746450691343101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033104058328600921790801 1524828043746450691343101)
                      ·
                        rfl

theorem cell23_2969592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 4, 2, 1, 4, 2].length) (baseStart_2969592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969592 prefixEnd_2969592 := by exact prefixLift 2969592
  have htrace : WordTrace (prefixWord ++ tailWord_2969592) baseStart_2969592 baseEnd_2969592 := by
    simpa [prefixWord, tailWord_2969592, baseEnd_2969592] using wordTrace_append hprefix tailTrace_2969592
  have hstable : (prefixWord ++ tailWord_2969592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969592).length < 2 ^ (prefixWord ++ tailWord_2969592).sum := by decide
  have hdescent : baseEnd_2969592 < baseStart_2969592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969605 : List Nat := [1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 4]
def baseStart_2969605 : Nat := 118140960795 + 2969605 * 2 ^ 59
def prefixEnd_2969605 : Nat := 4983230072969 + 3 ^ 40 * 2969605 * 2
def baseEnd_2969605 : Nat := 1524834718994959140480541

theorem tailTrace_2969605 : CollatzResearch.WordTrace tailWord_2969605 prefixEnd_2969605 1524834718994959140480541 := by
  unfold tailWord_2969605
  simp only [CollatzResearch.WordTrace]
  refine ⟨108310392406635728001390269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72206928271090485334260179 108310392406635728001390269)
  ·
    refine ⟨40616397152488398000521351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108310392406635728001390269 40616397152488398000521351)
    ·
      refine ⟨60924595728732597000782027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40616397152488398000521351 60924595728732597000782027)
      ·
        refine ⟨91386893593098895501173041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60924595728732597000782027 91386893593098895501173041)
        ·
          refine ⟨68540170194824171625879781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91386893593098895501173041 68540170194824171625879781)
          ·
            refine ⟨12851281911529532179852459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68540170194824171625879781 12851281911529532179852459)
            ·
              refine ⟨19276922867294298269778689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12851281911529532179852459 19276922867294298269778689)
              ·
                refine ⟨14457692150470723702334017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19276922867294298269778689 14457692150470723702334017)
                ·
                  refine ⟨10843269112853042776750513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14457692150470723702334017 10843269112853042776750513)
                  ·
                    refine ⟨8132451834639782082562885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10843269112853042776750513 8132451834639782082562885)
                    ·
                      refine ⟨1524834718994959140480541, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8132451834639782082562885 1524834718994959140480541)
                      ·
                        rfl

theorem cell23_2969605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 4].length) (baseStart_2969605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969605 prefixEnd_2969605 := by exact prefixLift 2969605
  have htrace : WordTrace (prefixWord ++ tailWord_2969605) baseStart_2969605 baseEnd_2969605 := by
    simpa [prefixWord, tailWord_2969605, baseEnd_2969605] using wordTrace_append hprefix tailTrace_2969605
  have hstable : (prefixWord ++ tailWord_2969605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969605).length < 2 ^ (prefixWord ++ tailWord_2969605).sum := by decide
  have hdescent : baseEnd_2969605 < baseStart_2969605 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969620 : List Nat := [2, 4, 3, 2, 1, 1, 3, 1, 2, 1, 3]
def baseStart_2969620 : Nat := 118140960795 + 2969620 * 2 ^ 59
def prefixEnd_2969620 : Nat := 4983230072969 + 3 ^ 40 * 2969620 * 2
def baseEnd_2969620 : Nat := 1524842421204776581792973

theorem tailTrace_2969620 : CollatzResearch.WordTrace tailWord_2969620 prefixEnd_2969620 1524842421204776581792973 := by
  unfold tailWord_2969620
  simp only [CollatzResearch.WordTrace]
  refine ⟨54155469750790692781593157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72207293001054257042124209 54155469750790692781593157)
  ·
    refine ⟨10154150578273254896548717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54155469750790692781593157 10154150578273254896548717)
    ·
      refine ⟨3807806466852470586205769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10154150578273254896548717 3807806466852470586205769)
      ·
        refine ⟨2855854850139352939654327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3807806466852470586205769 2855854850139352939654327)
        ·
          refine ⟨4283782275209029409481491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855854850139352939654327 4283782275209029409481491)
          ·
            refine ⟨6425673412813544114222237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283782275209029409481491 6425673412813544114222237)
            ·
              refine ⟨2409627529805079042833339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6425673412813544114222237 2409627529805079042833339)
              ·
                refine ⟨3614441294707618564250009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2409627529805079042833339 3614441294707618564250009)
                ·
                  refine ⟨2710830971030713923187507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3614441294707618564250009 2710830971030713923187507)
                  ·
                    refine ⟨4066246456546070884781261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2710830971030713923187507 4066246456546070884781261)
                    ·
                      refine ⟨1524842421204776581792973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066246456546070884781261 1524842421204776581792973)
                      ·
                        rfl

theorem cell23_2969620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 3, 1, 2, 1, 3].length) (baseStart_2969620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969620 prefixEnd_2969620 := by exact prefixLift 2969620
  have htrace : WordTrace (prefixWord ++ tailWord_2969620) baseStart_2969620 baseEnd_2969620 := by
    simpa [prefixWord, tailWord_2969620, baseEnd_2969620] using wordTrace_append hprefix tailTrace_2969620
  have hstable : (prefixWord ++ tailWord_2969620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969620).length < 2 ^ (prefixWord ++ tailWord_2969620).sum := by decide
  have hdescent : baseEnd_2969620 < baseStart_2969620 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969649 : List Nat := [1, 2, 2, 3, 1, 5, 1, 3, 5]
def baseStart_2969649 : Nat := 118140960795 + 2969649 * 2 ^ 59
def prefixEnd_2969649 : Nat := 4983230072969 + 3 ^ 40 * 2969649 * 2
def baseEnd_2969649 : Nat := 169428590238195218703371

theorem tailTrace_2969649 : CollatzResearch.WordTrace tailWord_2969649 prefixEnd_2969649 169428590238195218703371 := by
  unfold tailWord_2969649
  simp only [CollatzResearch.WordTrace]
  refine ⟨108311997218476323515992001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72207998145650882343994667 108311997218476323515992001)
  ·
    refine ⟨81233997913857242636994001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108311997218476323515992001 81233997913857242636994001)
    ·
      refine ⟨60925498435392931977745501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81233997913857242636994001 60925498435392931977745501)
      ·
        refine ⟨22847061913272349491654563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60925498435392931977745501 22847061913272349491654563)
        ·
          refine ⟨34270592869908524237481845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22847061913272349491654563 34270592869908524237481845)
          ·
            refine ⟨3212868081553924147263923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34270592869908524237481845 3212868081553924147263923)
            ·
              refine ⟨4819302122330886220895885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3212868081553924147263923 4819302122330886220895885)
              ·
                refine ⟨1807238295874082332835957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4819302122330886220895885 1807238295874082332835957)
                ·
                  refine ⟨169428590238195218703371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807238295874082332835957 169428590238195218703371)
                  ·
                    rfl

theorem cell23_2969649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 3, 5].length) (baseStart_2969649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969649 prefixEnd_2969649 := by exact prefixLift 2969649
  have htrace : WordTrace (prefixWord ++ tailWord_2969649) baseStart_2969649 baseEnd_2969649 := by
    simpa [prefixWord, tailWord_2969649, baseEnd_2969649] using wordTrace_append hprefix tailTrace_2969649
  have hstable : (prefixWord ++ tailWord_2969649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969649).length < 2 ^ (prefixWord ++ tailWord_2969649).sum := by decide
  have hdescent : baseEnd_2969649 < baseStart_2969649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969749 : List Nat := [1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 3]
def baseStart_2969749 : Nat := 118140960795 + 2969749 * 2 ^ 59
def prefixEnd_2969749 : Nat := 4983230072969 + 3 ^ 40 * 2969749 * 2
def baseEnd_2969749 : Nat := 1524908660209206577079879

theorem tailTrace_2969749 : CollatzResearch.WordTrace tailWord_2969749 prefixEnd_2969749 1524908660209206577079879 := by
  unfold tailWord_2969749
  simp only [CollatzResearch.WordTrace]
  refine ⟨108315644518114040594632301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72210429678742693729754867 108315644518114040594632301)
  ·
    refine ⟨40618366694292765222987113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108315644518114040594632301 40618366694292765222987113)
    ·
      refine ⟨30463775020719573917240335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40618366694292765222987113 30463775020719573917240335)
      ·
        refine ⟨45695662531079360875860503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30463775020719573917240335 45695662531079360875860503)
        ·
          refine ⟨68543493796619041313790755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45695662531079360875860503 68543493796619041313790755)
          ·
            refine ⟨102815240694928561970686133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68543493796619041313790755 102815240694928561970686133)
            ·
              refine ⟨9638928815149552684751825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102815240694928561970686133 9638928815149552684751825)
              ·
                refine ⟨7229196611362164513563869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9638928815149552684751825 7229196611362164513563869)
                ·
                  refine ⟨2710948729260811692586451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7229196611362164513563869 2710948729260811692586451)
                  ·
                    refine ⟨4066423093891217538879677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2710948729260811692586451 4066423093891217538879677)
                    ·
                      refine ⟨1524908660209206577079879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066423093891217538879677 1524908660209206577079879)
                      ·
                        rfl

theorem cell23_2969749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 5, 2, 3, 1, 3].length) (baseStart_2969749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969749 prefixEnd_2969749 := by exact prefixLift 2969749
  have htrace : WordTrace (prefixWord ++ tailWord_2969749) baseStart_2969749 baseEnd_2969749 := by
    simpa [prefixWord, tailWord_2969749, baseEnd_2969749] using wordTrace_append hprefix tailTrace_2969749
  have hstable : (prefixWord ++ tailWord_2969749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969749).length < 2 ^ (prefixWord ++ tailWord_2969749).sum := by decide
  have hdescent : baseEnd_2969749 < baseStart_2969749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969750 : List Nat := [5, 3, 2, 1, 1, 1, 1, 1, 1, 3, 4]
def baseStart_2969750 : Nat := 118140960795 + 2969750 * 2 ^ 59
def prefixEnd_2969750 : Nat := 4983230072969 + 3 ^ 40 * 2969750 * 2
def baseEnd_2969750 : Nat := 1524909173689861073167375

theorem tailTrace_2969750 : CollatzResearch.WordTrace tailWord_2969750 prefixEnd_2969750 1524909173689861073167375 := by
  unfold tailWord_2969750
  simp only [CollatzResearch.WordTrace]
  refine ⟨6769730061944401110338669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72210453994073611843612469 6769730061944401110338669)
  ·
    refine ⟨2538648773229150416377001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6769730061944401110338669 2538648773229150416377001)
    ·
      refine ⟨1903986579921862812282751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2538648773229150416377001 1903986579921862812282751)
      ·
        refine ⟨2855979869882794218424127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1903986579921862812282751 2855979869882794218424127)
        ·
          refine ⟨4283969804824191327636191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2855979869882794218424127 4283969804824191327636191)
          ·
            refine ⟨6425954707236286991454287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4283969804824191327636191 6425954707236286991454287)
            ·
              refine ⟨9638932060854430487181431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6425954707236286991454287 9638932060854430487181431)
              ·
                refine ⟨14458398091281645730772147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9638932060854430487181431 14458398091281645730772147)
                ·
                  refine ⟨21687597136922468596158221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14458398091281645730772147 21687597136922468596158221)
                  ·
                    refine ⟨8132848926345925723559333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21687597136922468596158221 8132848926345925723559333)
                    ·
                      refine ⟨1524909173689861073167375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8132848926345925723559333 1524909173689861073167375)
                      ·
                        rfl

theorem cell23_2969750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 1, 1, 3, 4].length) (baseStart_2969750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969750 prefixEnd_2969750 := by exact prefixLift 2969750
  have htrace : WordTrace (prefixWord ++ tailWord_2969750) baseStart_2969750 baseEnd_2969750 := by
    simpa [prefixWord, tailWord_2969750, baseEnd_2969750] using wordTrace_append hprefix tailTrace_2969750
  have hstable : (prefixWord ++ tailWord_2969750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969750).length < 2 ^ (prefixWord ++ tailWord_2969750).sum := by decide
  have hdescent : baseEnd_2969750 < baseStart_2969750 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969755 : List Nat := [1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4]
def baseStart_2969755 : Nat := 118140960795 + 2969755 * 2 ^ 59
def prefixEnd_2969755 : Nat := 4983230072969 + 3 ^ 40 * 2969755 * 2
def baseEnd_2969755 : Nat := 1524911741093133553604851

theorem tailTrace_2969755 : CollatzResearch.WordTrace tailWord_2969755 prefixEnd_2969755 1524911741093133553604851 := by
  unfold tailWord_2969755
  simp only [CollatzResearch.WordTrace]
  refine ⟨108315863356092303619350719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72210575570728202412900479 108315863356092303619350719)
  ·
    refine ⟨162473795034138455429026079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108315863356092303619350719 162473795034138455429026079)
    ·
      refine ⟨243710692551207683143539119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162473795034138455429026079 243710692551207683143539119)
      ·
        refine ⟨365566038826811524715308679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243710692551207683143539119 365566038826811524715308679)
        ·
          refine ⟨548349058240217287072963019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365566038826811524715308679 548349058240217287072963019)
          ·
            refine ⟨822523587360325930609444529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548349058240217287072963019 822523587360325930609444529)
            ·
              refine ⟨616892690520244447957083397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 822523587360325930609444529 616892690520244447957083397)
              ·
                refine ⟨115667379472545833991953137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 616892690520244447957083397 115667379472545833991953137)
                ·
                  refine ⟨86750534604409375493964853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115667379472545833991953137 86750534604409375493964853)
                  ·
                    refine ⟨8132862619163378952559205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 86750534604409375493964853 8132862619163378952559205)
                    ·
                      refine ⟨1524911741093133553604851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8132862619163378952559205 1524911741093133553604851)
                      ·
                        rfl

theorem cell23_2969755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 5, 4].length) (baseStart_2969755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969755 prefixEnd_2969755 := by exact prefixLift 2969755
  have htrace : WordTrace (prefixWord ++ tailWord_2969755) baseStart_2969755 baseEnd_2969755 := by
    simpa [prefixWord, tailWord_2969755, baseEnd_2969755] using wordTrace_append hprefix tailTrace_2969755
  have hstable : (prefixWord ++ tailWord_2969755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969755).length < 2 ^ (prefixWord ++ tailWord_2969755).sum := by decide
  have hdescent : baseEnd_2969755 < baseStart_2969755 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969792 : List Nat := [2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5]
def baseStart_2969792 : Nat := 118140960795 + 2969792 * 2 ^ 59
def prefixEnd_2969792 : Nat := 4983230072969 + 3 ^ 40 * 2969792 * 2
def baseEnd_2969792 : Nat := 1524930739877349908842181

theorem tailTrace_2969792 : CollatzResearch.WordTrace tailWord_2969792 prefixEnd_2969792 1524930739877349908842181 := by
  unfold tailWord_2969792
  simp only [CollatzResearch.WordTrace]
  refine ⟨54158606428479129469223815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72211475237972172625631753 54158606428479129469223815)
  ·
    refine ⟨81237909642718694203835723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54158606428479129469223815 81237909642718694203835723)
    ·
      refine ⟨121856864464078041305753585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81237909642718694203835723 121856864464078041305753585)
      ·
        refine ⟨91392648348058530979315189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121856864464078041305753585 91392648348058530979315189)
        ·
          refine ⟨8568060782630487279310799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91392648348058530979315189 8568060782630487279310799)
          ·
            refine ⟨12852091173945730918966199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568060782630487279310799 12852091173945730918966199)
            ·
              refine ⟨19278136760918596378449299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12852091173945730918966199 19278136760918596378449299)
              ·
                refine ⟨28917205141377894567673949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19278136760918596378449299 28917205141377894567673949)
                ·
                  refine ⟨10843951928016710462877731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28917205141377894567673949 10843951928016710462877731)
                  ·
                    refine ⟨16265927892025065694316597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10843951928016710462877731 16265927892025065694316597)
                    ·
                      refine ⟨1524930739877349908842181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16265927892025065694316597 1524930739877349908842181)
                      ·
                        rfl

theorem cell23_2969792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 1, 1, 3, 1, 5].length) (baseStart_2969792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969792 prefixEnd_2969792 := by exact prefixLift 2969792
  have htrace : WordTrace (prefixWord ++ tailWord_2969792) baseStart_2969792 baseEnd_2969792 := by
    simpa [prefixWord, tailWord_2969792, baseEnd_2969792] using wordTrace_append hprefix tailTrace_2969792
  have hstable : (prefixWord ++ tailWord_2969792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969792).length < 2 ^ (prefixWord ++ tailWord_2969792).sum := by decide
  have hdescent : baseEnd_2969792 < baseStart_2969792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969802 : List Nat := [3, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6]
def baseStart_2969802 : Nat := 118140960795 + 2969802 * 2 ^ 59
def prefixEnd_2969802 : Nat := 4983230072969 + 3 ^ 40 * 2969802 * 2
def baseEnd_2969802 : Nat := 1524935874683894869717135

theorem tailTrace_2969802 : CollatzResearch.WordTrace tailWord_2969802 prefixEnd_2969802 1524935874683894869717135 := by
  unfold tailWord_2969802
  simp only [CollatzResearch.WordTrace]
  refine ⟨27079394396730507661577915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72211718391281353764207773 27079394396730507661577915)
  ·
    refine ⟨40619091595095761492366873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27079394396730507661577915 40619091595095761492366873)
    ·
      refine ⟨30464318696321821119275155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40619091595095761492366873 30464318696321821119275155)
      ·
        refine ⟨45696478044482731678912733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30464318696321821119275155 45696478044482731678912733)
        ·
          refine ⟨17136179266681024379592275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45696478044482731678912733 17136179266681024379592275)
          ·
            refine ⟨25704268900021536569388413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17136179266681024379592275 25704268900021536569388413)
            ·
              refine ⟨9639100837508076213520655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25704268900021536569388413 9639100837508076213520655)
              ·
                refine ⟨14458651256262114320280983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9639100837508076213520655 14458651256262114320280983)
                ·
                  refine ⟨21687976884393171480421475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14458651256262114320280983 21687976884393171480421475)
                  ·
                    refine ⟨32531965326589757220632213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21687976884393171480421475 32531965326589757220632213)
                    ·
                      refine ⟨1524935874683894869717135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32531965326589757220632213 1524935874683894869717135)
                      ·
                        rfl

theorem cell23_2969802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 1, 1, 6].length) (baseStart_2969802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969802 prefixEnd_2969802 := by exact prefixLift 2969802
  have htrace : WordTrace (prefixWord ++ tailWord_2969802) baseStart_2969802 baseEnd_2969802 := by
    simpa [prefixWord, tailWord_2969802, baseEnd_2969802] using wordTrace_append hprefix tailTrace_2969802
  have hstable : (prefixWord ++ tailWord_2969802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969802).length < 2 ^ (prefixWord ++ tailWord_2969802).sum := by decide
  have hdescent : baseEnd_2969802 < baseStart_2969802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969806 : List Nat := [4, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4]
def baseStart_2969806 : Nat := 118140960795 + 2969806 * 2 ^ 59
def prefixEnd_2969806 : Nat := 4983230072969 + 3 ^ 40 * 2969806 * 2
def baseEnd_2969806 : Nat := 1524937928606512854067117

theorem tailTrace_2969806 : CollatzResearch.WordTrace tailWord_2969806 prefixEnd_2969806 1524937928606512854067117 := by
  unfold tailWord_2969806
  simp only [CollatzResearch.WordTrace]
  refine ⟨13539715434863442416182159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72211815652605026219638181 13539715434863442416182159)
  ·
    refine ⟨20309573152295163624273239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13539715434863442416182159 20309573152295163624273239)
    ·
      refine ⟨30464359728442745436409859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20309573152295163624273239 30464359728442745436409859)
      ·
        refine ⟨45696539592664118154614789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30464359728442745436409859 45696539592664118154614789)
        ·
          refine ⟨8568101173624522153990273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45696539592664118154614789 8568101173624522153990273)
          ·
            refine ⟨6426075880218391615492705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8568101173624522153990273 6426075880218391615492705)
            ·
              refine ⟨4819556910163793711619529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426075880218391615492705 4819556910163793711619529)
              ·
                refine ⟨3614667682622845283714647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819556910163793711619529 3614667682622845283714647)
                ·
                  refine ⟨5422001523934267925571971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614667682622845283714647 5422001523934267925571971)
                  ·
                    refine ⟨8133002285901401888357957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5422001523934267925571971 8133002285901401888357957)
                    ·
                      refine ⟨1524937928606512854067117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8133002285901401888357957 1524937928606512854067117)
                      ·
                        rfl

theorem cell23_2969806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 2, 2, 1, 1, 4].length) (baseStart_2969806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969806 prefixEnd_2969806 := by exact prefixLift 2969806
  have htrace : WordTrace (prefixWord ++ tailWord_2969806) baseStart_2969806 baseEnd_2969806 := by
    simpa [prefixWord, tailWord_2969806, baseEnd_2969806] using wordTrace_append hprefix tailTrace_2969806
  have hstable : (prefixWord ++ tailWord_2969806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969806).length < 2 ^ (prefixWord ++ tailWord_2969806).sum := by decide
  have hdescent : baseEnd_2969806 < baseStart_2969806 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969809 : List Nat := [1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 3]
def baseStart_2969809 : Nat := 118140960795 + 2969809 * 2 ^ 59
def prefixEnd_2969809 : Nat := 4983230072969 + 3 ^ 40 * 2969809 * 2
def baseEnd_2969809 : Nat := 1524939469048476342329603

theorem tailTrace_2969809 : CollatzResearch.WordTrace tailWord_2969809 prefixEnd_2969809 1524939469048476342329603 := by
  unfold tailWord_2969809
  simp only [CollatzResearch.WordTrace]
  refine ⟨108317832897896670841816481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72211888598597780561210987 108317832897896670841816481)
  ·
    refine ⟨81238374673422503131362361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108317832897896670841816481 81238374673422503131362361)
    ·
      refine ⟨60928781005066877348521771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81238374673422503131362361 60928781005066877348521771)
      ·
        refine ⟨91393171507600316022782657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60928781005066877348521771 91393171507600316022782657)
        ·
          refine ⟨68544878630700237017086993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91393171507600316022782657 68544878630700237017086993)
          ·
            refine ⟨51408658973025177762815245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68544878630700237017086993 51408658973025177762815245)
            ·
              refine ⟨19278247114884441661055717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51408658973025177762815245 19278247114884441661055717)
              ·
                refine ⟨3614671334040832811447947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19278247114884441661055717 3614671334040832811447947)
                ·
                  refine ⟨5422007001061249217171921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614671334040832811447947 5422007001061249217171921)
                  ·
                    refine ⟨4066505250795936912878941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5422007001061249217171921 4066505250795936912878941)
                    ·
                      refine ⟨1524939469048476342329603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066505250795936912878941 1524939469048476342329603)
                      ·
                        rfl

theorem cell23_2969809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 4, 1, 2, 3].length) (baseStart_2969809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969809 prefixEnd_2969809 := by exact prefixLift 2969809
  have htrace : WordTrace (prefixWord ++ tailWord_2969809) baseStart_2969809 baseEnd_2969809 := by
    simpa [prefixWord, tailWord_2969809, baseEnd_2969809] using wordTrace_append hprefix tailTrace_2969809
  have hstable : (prefixWord ++ tailWord_2969809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969809).length < 2 ^ (prefixWord ++ tailWord_2969809).sum := by decide
  have hdescent : baseEnd_2969809 < baseStart_2969809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969860 : List Nat := [2, 3, 2, 2, 4, 1, 1, 2, 1, 2, 3]
def baseStart_2969860 : Nat := 118140960795 + 2969860 * 2 ^ 59
def prefixEnd_2969860 : Nat := 4983230072969 + 3 ^ 40 * 2969860 * 2
def baseEnd_2969860 : Nat := 1524965656561855642791869

theorem tailTrace_2969860 : CollatzResearch.WordTrace tailWord_2969860 prefixEnd_2969860 1524965656561855642791869 := by
  unfold tailWord_2969860
  simp only [CollatzResearch.WordTrace]
  refine ⟨54159846510355953275961517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72213128680474604367948689 54159846510355953275961517)
  ·
    refine ⟨20309942441383482478485569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54159846510355953275961517 20309942441383482478485569)
    ·
      refine ⟨15232456831037611858864177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20309942441383482478485569 15232456831037611858864177)
      ·
        refine ⟨11424342623278208894148133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15232456831037611858864177 11424342623278208894148133)
        ·
          refine ⟨2142064241864664167652775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11424342623278208894148133 2142064241864664167652775)
          ·
            refine ⟨3213096362796996251479163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2142064241864664167652775 3213096362796996251479163)
            ·
              refine ⟨4819644544195494377218745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213096362796996251479163 4819644544195494377218745)
              ·
                refine ⟨3614733408146620782914059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4819644544195494377218745 3614733408146620782914059)
                ·
                  refine ⟨5422100112219931174371089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3614733408146620782914059 5422100112219931174371089)
                  ·
                    refine ⟨4066575084164948380778317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5422100112219931174371089 4066575084164948380778317)
                    ·
                      refine ⟨1524965656561855642791869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066575084164948380778317 1524965656561855642791869)
                      ·
                        rfl

theorem cell23_2969860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 1, 2, 1, 2, 3].length) (baseStart_2969860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969860 prefixEnd_2969860 := by exact prefixLift 2969860
  have htrace : WordTrace (prefixWord ++ tailWord_2969860) baseStart_2969860 baseEnd_2969860 := by
    simpa [prefixWord, tailWord_2969860, baseEnd_2969860] using wordTrace_append hprefix tailTrace_2969860
  have hstable : (prefixWord ++ tailWord_2969860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969860).length < 2 ^ (prefixWord ++ tailWord_2969860).sum := by decide
  have hdescent : baseEnd_2969860 < baseStart_2969860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969909 : List Nat := [1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 4]
def baseStart_2969909 : Nat := 118140960795 + 2969909 * 2 ^ 59
def prefixEnd_2969909 : Nat := 4983230072969 + 3 ^ 40 * 2969909 * 2
def baseEnd_2969909 : Nat := 1524990817113925951079143

theorem tailTrace_2969909 : CollatzResearch.WordTrace tailWord_2969909 prefixEnd_2969909 1524990817113925951079143 := by
  unfold tailWord_2969909
  simp only [CollatzResearch.WordTrace]
  refine ⟨108321480197534387920456781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72214320131689591946971187 108321480197534387920456781)
  ·
    refine ⟨40620555074075395470171293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108321480197534387920456781 40620555074075395470171293)
    ·
      refine ⟨15232708152778273301314235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40620555074075395470171293 15232708152778273301314235)
      ·
        refine ⟨22849062229167409951971353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15232708152778273301314235 22849062229167409951971353)
        ·
          refine ⟨17136796671875557463978515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22849062229167409951971353 17136796671875557463978515)
          ·
            refine ⟨25705195007813336195967773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17136796671875557463978515 25705195007813336195967773)
            ·
              refine ⟨9639448127930001073487915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25705195007813336195967773 9639448127930001073487915)
              ·
                refine ⟨14459172191895001610231873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9639448127930001073487915 14459172191895001610231873)
                ·
                  refine ⟨10844379143921251207673905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14459172191895001610231873 10844379143921251207673905)
                  ·
                    refine ⟨8133284357940938405755429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10844379143921251207673905 8133284357940938405755429)
                    ·
                      refine ⟨1524990817113925951079143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8133284357940938405755429 1524990817113925951079143)
                      ·
                        rfl

theorem cell23_2969909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 2, 4].length) (baseStart_2969909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969909 prefixEnd_2969909 := by exact prefixLift 2969909
  have htrace : WordTrace (prefixWord ++ tailWord_2969909) baseStart_2969909 baseEnd_2969909 := by
    simpa [prefixWord, tailWord_2969909, baseEnd_2969909] using wordTrace_append hprefix tailTrace_2969909
  have hstable : (prefixWord ++ tailWord_2969909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969909).length < 2 ^ (prefixWord ++ tailWord_2969909).sum := by decide
  have hdescent : baseEnd_2969909 < baseStart_2969909 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969913 : List Nat := [1, 2, 1, 6, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2969913 : Nat := 118140960795 + 2969913 * 2 ^ 59
def prefixEnd_2969913 : Nat := 4983230072969 + 3 ^ 40 * 2969913 * 2
def baseEnd_2969913 : Nat := 1524992871036543935429125

theorem tailTrace_2969913 : CollatzResearch.WordTrace tailWord_2969913 prefixEnd_2969913 1524992871036543935429125 := by
  unfold tailWord_2969913
  simp only [CollatzResearch.WordTrace]
  refine ⟨108321626089519896603602393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72214417393013264402401595 108321626089519896603602393)
  ·
    refine ⟨81241219567139922452701795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108321626089519896603602393 81241219567139922452701795)
    ·
      refine ⟨121861829350709883679052693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81241219567139922452701795 121861829350709883679052693)
      ·
        refine ⟨5712273250814525797455595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121861829350709883679052693 5712273250814525797455595)
        ·
          refine ⟨8568409876221788696183393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712273250814525797455595 8568409876221788696183393)
          ·
            refine ⟨6426307407166341522137545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8568409876221788696183393 6426307407166341522137545)
            ·
              refine ⟨4819730555374756141603159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426307407166341522137545 4819730555374756141603159)
              ·
                refine ⟨7229595833062134212404739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4819730555374756141603159 7229595833062134212404739)
                ·
                  refine ⟨10844393749593201318607109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7229595833062134212404739 10844393749593201318607109)
                  ·
                    refine ⟨2033323828048725247238833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10844393749593201318607109 2033323828048725247238833)
                    ·
                      refine ⟨1524992871036543935429125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033323828048725247238833 1524992871036543935429125)
                      ·
                        rfl

theorem cell23_2969913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2969913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969913 prefixEnd_2969913 := by exact prefixLift 2969913
  have htrace : WordTrace (prefixWord ++ tailWord_2969913) baseStart_2969913 baseEnd_2969913 := by
    simpa [prefixWord, tailWord_2969913, baseEnd_2969913] using wordTrace_append hprefix tailTrace_2969913
  have hstable : (prefixWord ++ tailWord_2969913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969913).length < 2 ^ (prefixWord ++ tailWord_2969913).sum := by decide
  have hdescent : baseEnd_2969913 < baseStart_2969913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969936 : List Nat := [2, 1, 1, 1, 1, 7, 2, 3, 5]
def baseStart_2969936 : Nat := 118140960795 + 2969936 * 2 ^ 59
def prefixEnd_2969936 : Nat := 4983230072969 + 3 ^ 40 * 2969936 * 2
def baseEnd_2969936 : Nat := 169444964565733038382391

theorem tailTrace_2969936 : CollatzResearch.WordTrace tailWord_2969936 prefixEnd_2969936 169444964565733038382391 := by
  unfold tailWord_2969936
  simp only [CollatzResearch.WordTrace]
  refine ⟨54161232484218285765844831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72214976645624381021126441 54161232484218285765844831)
  ·
    refine ⟨81241848726327428648767247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54161232484218285765844831 81241848726327428648767247)
    ·
      refine ⟨121862773089491142973150871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81241848726327428648767247 121862773089491142973150871)
      ·
        refine ⟨182794159634236714459726307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121862773089491142973150871 182794159634236714459726307)
        ·
          refine ⟨274191239451355071689589461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182794159634236714459726307 274191239451355071689589461)
          ·
            refine ⟨6426357174641134492724753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 274191239451355071689589461 6426357174641134492724753)
            ·
              refine ⟨4819767880980850869543565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6426357174641134492724753 4819767880980850869543565)
              ·
                refine ⟨1807412955367819076078837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4819767880980850869543565 1807412955367819076078837)
                ·
                  refine ⟨169444964565733038382391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807412955367819076078837 169444964565733038382391)
                  ·
                    rfl

theorem cell23_2969936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 5].length) (baseStart_2969936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969936 prefixEnd_2969936 := by exact prefixLift 2969936
  have htrace : WordTrace (prefixWord ++ tailWord_2969936) baseStart_2969936 baseEnd_2969936 := by
    simpa [prefixWord, tailWord_2969936, baseEnd_2969936] using wordTrace_append hprefix tailTrace_2969936
  have hstable : (prefixWord ++ tailWord_2969936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969936).length < 2 ^ (prefixWord ++ tailWord_2969936).sum := by decide
  have hdescent : baseEnd_2969936 < baseStart_2969936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2969939 : List Nat := [1, 1, 1, 2, 1, 1, 4, 2, 1, 7, 2]
def baseStart_2969939 : Nat := 118140960795 + 2969939 * 2 ^ 59
def prefixEnd_2969939 : Nat := 4983230072969 + 3 ^ 40 * 2969939 * 2
def baseEnd_2969939 : Nat := 1525006221533560833704005

theorem tailTrace_2969939 : CollatzResearch.WordTrace tailWord_2969939 prefixEnd_2969939 1525006221533560833704005 := by
  unfold tailWord_2969939
  simp only [CollatzResearch.WordTrace]
  refine ⟨108322574387425703044048871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72215049591617135362699247 108322574387425703044048871)
  ·
    refine ⟨162483861581138554566073307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108322574387425703044048871 162483861581138554566073307)
    ·
      refine ⟨243725792371707831849109961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162483861581138554566073307 243725792371707831849109961)
      ·
        refine ⟨182794344278780873886832471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243725792371707831849109961 182794344278780873886832471)
        ·
          refine ⟨274191516418171310830248707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182794344278780873886832471 274191516418171310830248707)
          ·
            refine ⟨411287274627256966245373061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274191516418171310830248707 411287274627256966245373061)
            ·
              refine ⟨77116363992610681171007449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411287274627256966245373061 77116363992610681171007449)
              ·
                refine ⟨57837272994458010878255587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77116363992610681171007449 57837272994458010878255587)
                ·
                  refine ⟨86755909491687016317383381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57837272994458010878255587 86755909491687016317383381)
                  ·
                    refine ⟨2033341628711414444938673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86755909491687016317383381 2033341628711414444938673)
                    ·
                      refine ⟨1525006221533560833704005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033341628711414444938673 1525006221533560833704005)
                      ·
                        rfl

theorem cell23_2969939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 7, 2].length) (baseStart_2969939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2969939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2969939 prefixEnd_2969939 := by exact prefixLift 2969939
  have htrace : WordTrace (prefixWord ++ tailWord_2969939) baseStart_2969939 baseEnd_2969939 := by
    simpa [prefixWord, tailWord_2969939, baseEnd_2969939] using wordTrace_append hprefix tailTrace_2969939
  have hstable : (prefixWord ++ tailWord_2969939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2969939).length < 2 ^ (prefixWord ++ tailWord_2969939).sum := by decide
  have hdescent : baseEnd_2969939 < baseStart_2969939 := by decide
  rcases family_descends (prefixWord ++ tailWord_2969939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970009 : List Nat := [1, 2, 1, 2, 1, 4, 2, 4, 6]
def baseStart_2970009 : Nat := 118140960795 + 2970009 * 2 ^ 59
def prefixEnd_2970009 : Nat := 4983230072969 + 3 ^ 40 * 2970009 * 2
def baseEnd_2970009 : Nat := 169449129464375062203187

theorem tailTrace_2970009 : CollatzResearch.WordTrace tailWord_2970009 prefixEnd_2970009 169449129464375062203187 := by
  unfold tailWord_2970009
  simp only [CollatzResearch.WordTrace]
  refine ⟨108325127497172104999097081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72216751664781403332731387 108325127497172104999097081)
  ·
    refine ⟨81243845622879078749322811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108325127497172104999097081 81243845622879078749322811)
    ·
      refine ⟨121865768434318618123984217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81243845622879078749322811 121865768434318618123984217)
      ·
        refine ⟨91399326325738963592988163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121865768434318618123984217 91399326325738963592988163)
        ·
          refine ⟨137098989488608445389482245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91399326325738963592988163 137098989488608445389482245)
          ·
            refine ⟨25706060529114083510527921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 137098989488608445389482245 25706060529114083510527921)
            ·
              refine ⟨19279545396835562632895941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25706060529114083510527921 19279545396835562632895941)
              ·
                refine ⟨3614914761906667993667989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19279545396835562632895941 3614914761906667993667989)
                ·
                  refine ⟨169449129464375062203187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3614914761906667993667989 169449129464375062203187)
                  ·
                    rfl

theorem cell23_2970009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 2, 4, 6].length) (baseStart_2970009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970009 prefixEnd_2970009 := by exact prefixLift 2970009
  have htrace : WordTrace (prefixWord ++ tailWord_2970009) baseStart_2970009 baseEnd_2970009 := by
    simpa [prefixWord, tailWord_2970009, baseEnd_2970009] using wordTrace_append hprefix tailTrace_2970009
  have hstable : (prefixWord ++ tailWord_2970009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970009).length < 2 ^ (prefixWord ++ tailWord_2970009).sum := by decide
  have hdescent : baseEnd_2970009 < baseStart_2970009 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970070 : List Nat := [5, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3]
def baseStart_2970070 : Nat := 118140960795 + 2970070 * 2 ^ 59
def prefixEnd_2970070 : Nat := 4983230072969 + 3 ^ 40 * 2970070 * 2
def baseEnd_2970070 : Nat := 1525073487499299821165903

theorem tailTrace_2970070 : CollatzResearch.WordTrace tailWord_2970070 prefixEnd_2970070 1525073487499299821165903 := by
  unfold tailWord_2970070
  simp only [CollatzResearch.WordTrace]
  refine ⟨6770459521871944526066729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72218234899967408278045109 6770459521871944526066729)
  ·
    refine ⟨5077844641403958394550047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6770459521871944526066729 5077844641403958394550047)
    ·
      refine ⟨7616766962105937591825071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5077844641403958394550047 7616766962105937591825071)
      ·
        refine ⟨11425150443158906387737607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7616766962105937591825071 11425150443158906387737607)
        ·
          refine ⟨17137725664738359581606411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11425150443158906387737607 17137725664738359581606411)
          ·
            refine ⟨25706588497107539372409617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17137725664738359581606411 25706588497107539372409617)
            ·
              refine ⟨19279941372830654529307213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25706588497107539372409617 19279941372830654529307213)
              ·
                refine ⟨7229978014811495448490205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19279941372830654529307213 7229978014811495448490205)
                ·
                  refine ⟨2711241755554310793183827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7229978014811495448490205 2711241755554310793183827)
                  ·
                    refine ⟨4066862633331466189775741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2711241755554310793183827 4066862633331466189775741)
                    ·
                      refine ⟨1525073487499299821165903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066862633331466189775741 1525073487499299821165903)
                      ·
                        rfl

theorem cell23_2970070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 2, 3, 3, 1, 3].length) (baseStart_2970070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970070 prefixEnd_2970070 := by exact prefixLift 2970070
  have htrace : WordTrace (prefixWord ++ tailWord_2970070) baseStart_2970070 baseEnd_2970070 := by
    simpa [prefixWord, tailWord_2970070, baseEnd_2970070] using wordTrace_append hprefix tailTrace_2970070
  have hstable : (prefixWord ++ tailWord_2970070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970070).length < 2 ^ (prefixWord ++ tailWord_2970070).sum := by decide
  have hdescent : baseEnd_2970070 < baseStart_2970070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970093 : List Nat := [1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 4]
def baseStart_2970093 : Nat := 118140960795 + 2970093 * 2 ^ 59
def prefixEnd_2970093 : Nat := 4983230072969 + 3 ^ 40 * 2970093 * 2
def baseEnd_2970093 : Nat := 1525085297554353231178297

theorem tailTrace_2970093 : CollatzResearch.WordTrace tailWord_2970093 prefixEnd_2970093 1525085297554353231178297 := by
  unfold tailWord_2970093
  simp only [CollatzResearch.WordTrace]
  refine ⟨108328191228867787345154933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72218794152578524896769955 108328191228867787345154933)
  ·
    refine ⟨10155767927706355063608275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108328191228867787345154933 10155767927706355063608275)
    ·
      refine ⟨15233651891559532595412413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10155767927706355063608275 15233651891559532595412413)
      ·
        refine ⟨5712619459334824723279655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15233651891559532595412413 5712619459334824723279655)
        ·
          refine ⟨8568929189002237084919483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712619459334824723279655 8568929189002237084919483)
          ·
            refine ⟨12853393783503355627379225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8568929189002237084919483 12853393783503355627379225)
            ·
              refine ⟨9640045337627516720534419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12853393783503355627379225 9640045337627516720534419)
              ·
                refine ⟨14460068006441275080801629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640045337627516720534419 14460068006441275080801629)
                ·
                  refine ⟨5422525502415478155300611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14460068006441275080801629 5422525502415478155300611)
                  ·
                    refine ⟨8133788253623217232950917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5422525502415478155300611 8133788253623217232950917)
                    ·
                      refine ⟨1525085297554353231178297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8133788253623217232950917 1525085297554353231178297)
                      ·
                        rfl

theorem cell23_2970093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 4].length) (baseStart_2970093 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970093 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970093 prefixEnd_2970093 := by exact prefixLift 2970093
  have htrace : WordTrace (prefixWord ++ tailWord_2970093) baseStart_2970093 baseEnd_2970093 := by
    simpa [prefixWord, tailWord_2970093, baseEnd_2970093] using wordTrace_append hprefix tailTrace_2970093
  have hstable : (prefixWord ++ tailWord_2970093).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970093).length < 2 ^ (prefixWord ++ tailWord_2970093).sum := by decide
  have hdescent : baseEnd_2970093 < baseStart_2970093 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970096 : List Nat := [2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3]
def baseStart_2970096 : Nat := 118140960795 + 2970096 * 2 ^ 59
def prefixEnd_2970096 : Nat := 4983230072969 + 3 ^ 40 * 2970096 * 2
def baseEnd_2970096 : Nat := 1525086837996316719440783

theorem tailTrace_2970096 : CollatzResearch.WordTrace tailWord_2970096 prefixEnd_2970096 1525086837996316719440783 := by
  unfold tailWord_2970096
  simp only [CollatzResearch.WordTrace]
  refine ⟨54164150323928459428757071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72218867098571279238342761 54164150323928459428757071)
  ·
    refine ⟨81246225485892689143135607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54164150323928459428757071 81246225485892689143135607)
    ·
      refine ⟨121869338228839033714703411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81246225485892689143135607 121869338228839033714703411)
      ·
        refine ⟨182804007343258550572055117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121869338228839033714703411 182804007343258550572055117)
        ·
          refine ⟨68551502753721956464520669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182804007343258550572055117 68551502753721956464520669)
          ·
            refine ⟨25706813532645733674195251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68551502753721956464520669 25706813532645733674195251)
            ·
              refine ⟨38560220298968600511292877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25706813532645733674195251 38560220298968600511292877)
              ·
                refine ⟨14460082612113225191734829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38560220298968600511292877 14460082612113225191734829)
                ·
                  refine ⟨5422530979542459446900561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14460082612113225191734829 5422530979542459446900561)
                  ·
                    refine ⟨4066898234656844585175421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5422530979542459446900561 4066898234656844585175421)
                    ·
                      refine ⟨1525086837996316719440783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4066898234656844585175421 1525086837996316719440783)
                      ·
                        rfl

theorem cell23_2970096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 3, 3, 2, 3].length) (baseStart_2970096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970096 prefixEnd_2970096 := by exact prefixLift 2970096
  have htrace : WordTrace (prefixWord ++ tailWord_2970096) baseStart_2970096 baseEnd_2970096 := by
    simpa [prefixWord, tailWord_2970096, baseEnd_2970096] using wordTrace_append hprefix tailTrace_2970096
  have hstable : (prefixWord ++ tailWord_2970096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970096).length < 2 ^ (prefixWord ++ tailWord_2970096).sum := by decide
  have hdescent : baseEnd_2970096 < baseStart_2970096 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970116 : List Nat := [2, 3, 2, 3, 1, 2, 10]
def baseStart_2970116 : Nat := 118140960795 + 2970116 * 2 ^ 59
def prefixEnd_2970116 : Nat := 4983230072969 + 3 ^ 40 * 2970116 * 2
def baseEnd_2970116 : Nat := 18828359353202551125811

theorem tailTrace_2970116 : CollatzResearch.WordTrace tailWord_2970116 prefixEnd_2970116 18828359353202551125811 := by
  unfold tailWord_2970116
  simp only [CollatzResearch.WordTrace]
  refine ⟨54164515053892231136621101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72219353405189641515494801 54164515053892231136621101)
  ·
    refine ⟨20311693145209586676232913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54164515053892231136621101 20311693145209586676232913)
    ·
      refine ⟨15233769858907190007174685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20311693145209586676232913 15233769858907190007174685)
      ·
        refine ⟨5712663697090196252690507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15233769858907190007174685 5712663697090196252690507)
        ·
          refine ⟨8568995545635294379035761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5712663697090196252690507 8568995545635294379035761)
          ·
            refine ⟨6426746659226470784276821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8568995545635294379035761 6426746659226470784276821)
            ·
              refine ⟨18828359353202551125811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6426746659226470784276821 18828359353202551125811)
              ·
                rfl

theorem cell23_2970116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 10].length) (baseStart_2970116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970116 prefixEnd_2970116 := by exact prefixLift 2970116
  have htrace : WordTrace (prefixWord ++ tailWord_2970116) baseStart_2970116 baseEnd_2970116 := by
    simpa [prefixWord, tailWord_2970116, baseEnd_2970116] using wordTrace_append hprefix tailTrace_2970116
  have hstable : (prefixWord ++ tailWord_2970116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970116).length < 2 ^ (prefixWord ++ tailWord_2970116).sum := by decide
  have hdescent : baseEnd_2970116 < baseStart_2970116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970129 : List Nat := [1, 2, 2, 1, 1, 2, 2, 3, 2, 7]
def baseStart_2970129 : Nat := 118140960795 + 2970129 * 2 ^ 59
def prefixEnd_2970129 : Nat := 4983230072969 + 3 ^ 40 * 2970129 * 2
def baseEnd_2970129 : Nat := 508367927619305030109377

theorem tailTrace_2970129 : CollatzResearch.WordTrace tailWord_2970129 prefixEnd_2970129 508367927619305030109377 := by
  unfold tailWord_2970129
  simp only [CollatzResearch.WordTrace]
  refine ⟨108329504256737365493465441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72219669504491576995643627 108329504256737365493465441)
  ·
    refine ⟨81247128192553024120099081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108329504256737365493465441 81247128192553024120099081)
    ·
      refine ⟨60935346144414768090074311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81247128192553024120099081 60935346144414768090074311)
      ·
        refine ⟨91403019216622152135111467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60935346144414768090074311 91403019216622152135111467)
        ·
          refine ⟨137104528824933228202667201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91403019216622152135111467 137104528824933228202667201)
          ·
            refine ⟨102828396618699921152000401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137104528824933228202667201 102828396618699921152000401)
            ·
              refine ⟨77121297464024940864000301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102828396618699921152000401 77121297464024940864000301)
              ·
                refine ⟨28920486549009352824000113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77121297464024940864000301 28920486549009352824000113)
                ·
                  refine ⟨21690364911757014618000085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28920486549009352824000113 21690364911757014618000085)
                  ·
                    refine ⟨508367927619305030109377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21690364911757014618000085 508367927619305030109377)
                    ·
                      rfl

theorem cell23_2970129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 7].length) (baseStart_2970129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970129 prefixEnd_2970129 := by exact prefixLift 2970129
  have htrace : WordTrace (prefixWord ++ tailWord_2970129) baseStart_2970129 baseEnd_2970129 := by
    simpa [prefixWord, tailWord_2970129, baseEnd_2970129] using wordTrace_append hprefix tailTrace_2970129
  have hstable : (prefixWord ++ tailWord_2970129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970129).length < 2 ^ (prefixWord ++ tailWord_2970129).sum := by decide
  have hdescent : baseEnd_2970129 < baseStart_2970129 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970139 : List Nat := [1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5]
def baseStart_2970139 : Nat := 118140960795 + 2970139 * 2 ^ 59
def prefixEnd_2970139 : Nat := 4983230072969 + 3 ^ 40 * 2970139 * 2
def baseEnd_2970139 : Nat := 1525108917664460051203085

theorem tailTrace_2970139 : CollatzResearch.WordTrace tailWord_2970139 prefixEnd_2970139 1525108917664460051203085 := by
  unfold tailWord_2970139
  simp only [CollatzResearch.WordTrace]
  refine ⟨108329868986701137201329471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72219912657800758134219647 108329868986701137201329471)
  ·
    refine ⟨162494803480051705801994207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108329868986701137201329471 162494803480051705801994207)
    ·
      refine ⟨243742205220077558702991311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162494803480051705801994207 243742205220077558702991311)
      ·
        refine ⟨365613307830116338054486967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243742205220077558702991311 365613307830116338054486967)
        ·
          refine ⟨548419961745174507081730451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365613307830116338054486967 548419961745174507081730451)
          ·
            refine ⟨822629942617761760622595677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548419961745174507081730451 822629942617761760622595677)
            ·
              refine ⟨308486228481660660233473379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 822629942617761760622595677 308486228481660660233473379)
              ·
                refine ⟨462729342722490990350210069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308486228481660660233473379 462729342722490990350210069)
                ·
                  refine ⟨21690437940116765172666097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 462729342722490990350210069 21690437940116765172666097)
                  ·
                    refine ⟨16267828455087573879499573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21690437940116765172666097 16267828455087573879499573)
                    ·
                      refine ⟨1525108917664460051203085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16267828455087573879499573 1525108917664460051203085)
                      ·
                        rfl

theorem cell23_2970139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_2970139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970139 prefixEnd_2970139 := by exact prefixLift 2970139
  have htrace : WordTrace (prefixWord ++ tailWord_2970139) baseStart_2970139 baseEnd_2970139 := by
    simpa [prefixWord, tailWord_2970139, baseEnd_2970139] using wordTrace_append hprefix tailTrace_2970139
  have hstable : (prefixWord ++ tailWord_2970139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970139).length < 2 ^ (prefixWord ++ tailWord_2970139).sum := by decide
  have hdescent : baseEnd_2970139 < baseStart_2970139 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970170 : List Nat := [3, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2]
def baseStart_2970170 : Nat := 118140960795 + 2970170 * 2 ^ 59
def prefixEnd_2970170 : Nat := 4983230072969 + 3 ^ 40 * 2970170 * 2
def baseEnd_2970170 : Nat := 1525124835564749429915443

theorem tailTrace_2970170 : CollatzResearch.WordTrace tailWord_2970170 prefixEnd_2970170 1525124835564749429915443 := by
  unfold tailWord_2970170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27082749912397207373926991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72220666433059219663805309 27082749912397207373926991)
  ·
    refine ⟨40624124868595811060890487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27082749912397207373926991 40624124868595811060890487)
    ·
      refine ⟨60936187302893716591335731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40624124868595811060890487 60936187302893716591335731)
      ·
        refine ⟨91404280954340574887003597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60936187302893716591335731 91404280954340574887003597)
        ·
          refine ⟨34276605357877715582626349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91404280954340574887003597 34276605357877715582626349)
          ·
            refine ⟨12853727009204143343484881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34276605357877715582626349 12853727009204143343484881)
            ·
              refine ⟨9640295256903107507613661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12853727009204143343484881 9640295256903107507613661)
              ·
                refine ⟨3615110721338665315355123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9640295256903107507613661 3615110721338665315355123)
                ·
                  refine ⟨5422666082007997973032685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615110721338665315355123 5422666082007997973032685)
                  ·
                    refine ⟨2033499780752999239887257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5422666082007997973032685 2033499780752999239887257)
                    ·
                      refine ⟨1525124835564749429915443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033499780752999239887257 1525124835564749429915443)
                      ·
                        rfl

theorem cell23_2970170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 3, 2, 3, 1, 3, 2].length) (baseStart_2970170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970170 prefixEnd_2970170 := by exact prefixLift 2970170
  have htrace : WordTrace (prefixWord ++ tailWord_2970170) baseStart_2970170 baseEnd_2970170 := by
    simpa [prefixWord, tailWord_2970170, baseEnd_2970170] using wordTrace_append hprefix tailTrace_2970170
  have hstable : (prefixWord ++ tailWord_2970170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970170).length < 2 ^ (prefixWord ++ tailWord_2970170).sum := by decide
  have hdescent : baseEnd_2970170 < baseStart_2970170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970204 : List Nat := [2, 2, 4, 1, 3, 2, 1, 2, 1, 3, 2]
def baseStart_2970204 : Nat := 118140960795 + 2970204 * 2 ^ 59
def prefixEnd_2970204 : Nat := 4983230072969 + 3 ^ 40 * 2970204 * 2
def baseEnd_2970204 : Nat := 1525142293907002296890287

theorem tailTrace_2970204 : CollatzResearch.WordTrace tailWord_2970204 prefixEnd_2970204 1525142293907002296890287 := by
  unfold tailWord_2970204
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166119865732826651222833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72221493154310435534963777 54166119865732826651222833)
  ·
    refine ⟨40624589899299619988417125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54166119865732826651222833 40624589899299619988417125)
    ·
      refine ⟨7617110606118678747828211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40624589899299619988417125 7617110606118678747828211)
      ·
        refine ⟨11425665909178018121742317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7617110606118678747828211 11425665909178018121742317)
        ·
          refine ⟨4284624715941756795653369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11425665909178018121742317 4284624715941756795653369)
          ·
            refine ⟨3213468536956317596740027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4284624715941756795653369 3213468536956317596740027)
            ·
              refine ⟨4820202805434476395110041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213468536956317596740027 4820202805434476395110041)
              ·
                refine ⟨3615152104075857296332531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820202805434476395110041 3615152104075857296332531)
                ·
                  refine ⟨5422728156113785944498797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615152104075857296332531 5422728156113785944498797)
                  ·
                    refine ⟨2033523058542669729187049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5422728156113785944498797 2033523058542669729187049)
                    ·
                      refine ⟨1525142293907002296890287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033523058542669729187049 1525142293907002296890287)
                      ·
                        rfl

theorem cell23_2970204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 1, 2, 1, 3, 2].length) (baseStart_2970204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970204 prefixEnd_2970204 := by exact prefixLift 2970204
  have htrace : WordTrace (prefixWord ++ tailWord_2970204) baseStart_2970204 baseEnd_2970204 := by
    simpa [prefixWord, tailWord_2970204, baseEnd_2970204] using wordTrace_append hprefix tailTrace_2970204
  have hstable : (prefixWord ++ tailWord_2970204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970204).length < 2 ^ (prefixWord ++ tailWord_2970204).sum := by decide
  have hdescent : baseEnd_2970204 < baseStart_2970204 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970240 : List Nat := [2, 1, 1, 2, 1, 5, 4, 2, 5]
def baseStart_2970240 : Nat := 118140960795 + 2970240 * 2 ^ 59
def prefixEnd_2970240 : Nat := 4983230072969 + 3 ^ 40 * 2970240 * 2
def baseEnd_2970240 : Nat := 169462308801173795115569

theorem tailTrace_2970240 : CollatzResearch.WordTrace tailWord_2970240 prefixEnd_2970240 169462308801173795115569 := by
  unfold tailWord_2970240
  simp only [CollatzResearch.WordTrace]
  refine ⟨54166776379667615725378087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72222368506223487633837449 54166776379667615725378087)
  ·
    refine ⟨81250164569501423588067131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54166776379667615725378087 81250164569501423588067131)
    ·
      refine ⟨121875246854252135382100697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81250164569501423588067131 121875246854252135382100697)
      ·
        refine ⟨91406435140689101536575523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121875246854252135382100697 91406435140689101536575523)
        ·
          refine ⟨137109652711033652304863285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91406435140689101536575523 137109652711033652304863285)
          ·
            refine ⟨12854029941659404903580933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 137109652711033652304863285 12854029941659404903580933)
            ·
              refine ⟨2410130614061138419421425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12854029941659404903580933 2410130614061138419421425)
              ·
                refine ⟨1807597960545853814566069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410130614061138419421425 1807597960545853814566069)
                ·
                  refine ⟨169462308801173795115569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1807597960545853814566069 169462308801173795115569)
                  ·
                    rfl

theorem cell23_2970240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 2, 5].length) (baseStart_2970240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970240 prefixEnd_2970240 := by exact prefixLift 2970240
  have htrace : WordTrace (prefixWord ++ tailWord_2970240) baseStart_2970240 baseEnd_2970240 := by
    simpa [prefixWord, tailWord_2970240, baseEnd_2970240] using wordTrace_append hprefix tailTrace_2970240
  have hstable : (prefixWord ++ tailWord_2970240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970240).length < 2 ^ (prefixWord ++ tailWord_2970240).sum := by decide
  have hdescent : baseEnd_2970240 < baseStart_2970240 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970243 : List Nat := [1, 1, 1, 3, 3, 1, 3, 1, 2, 5, 2]
def baseStart_2970243 : Nat := 118140960795 + 2970243 * 2 ^ 59
def prefixEnd_2970243 : Nat := 4983230072969 + 3 ^ 40 * 2970243 * 2
def baseEnd_2970243 : Nat := 1525162319652527644302607

theorem tailTrace_2970243 : CollatzResearch.WordTrace tailWord_2970243 prefixEnd_2970243 1525162319652527644302607 := by
  unfold tailWord_2970243
  simp only [CollatzResearch.WordTrace]
  refine ⟨108333662178324362963115383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72222441452216241975410255 108333662178324362963115383)
  ·
    refine ⟨162500493267486544444673075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108333662178324362963115383 162500493267486544444673075)
    ·
      refine ⟨243750739901229816667009613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162500493267486544444673075 243750739901229816667009613)
      ·
        refine ⟨91406527462961181250128605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243750739901229816667009613 91406527462961181250128605)
        ·
          refine ⟨34277447798610442968798227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91406527462961181250128605 34277447798610442968798227)
          ·
            refine ⟨51416171697915664453197341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34277447798610442968798227 51416171697915664453197341)
            ·
              refine ⟨19281064386718374169949003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51416171697915664453197341 19281064386718374169949003)
              ·
                refine ⟨28921596580077561254923505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19281064386718374169949003 28921596580077561254923505)
                ·
                  refine ⟨21691197435058170941192629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28921596580077561254923505 21691197435058170941192629)
                  ·
                    refine ⟨2033549759536703525736809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21691197435058170941192629 2033549759536703525736809)
                    ·
                      refine ⟨1525162319652527644302607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033549759536703525736809 1525162319652527644302607)
                      ·
                        rfl

theorem cell23_2970243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 5, 2].length) (baseStart_2970243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970243 prefixEnd_2970243 := by exact prefixLift 2970243
  have htrace : WordTrace (prefixWord ++ tailWord_2970243) baseStart_2970243 baseEnd_2970243 := by
    simpa [prefixWord, tailWord_2970243, baseEnd_2970243] using wordTrace_append hprefix tailTrace_2970243
  have hstable : (prefixWord ++ tailWord_2970243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970243).length < 2 ^ (prefixWord ++ tailWord_2970243).sum := by decide
  have hdescent : baseEnd_2970243 < baseStart_2970243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970250 : List Nat := [3, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3]
def baseStart_2970250 : Nat := 118140960795 + 2970250 * 2 ^ 59
def prefixEnd_2970250 : Nat := 4983230072969 + 3 ^ 40 * 2970250 * 2
def baseEnd_2970250 : Nat := 1525165914017109116915075

theorem tailTrace_2970250 : CollatzResearch.WordTrace tailWord_2970250 prefixEnd_2970250 1525165914017109116915075 := by
  unfold tailWord_2970250
  simp only [CollatzResearch.WordTrace]
  refine ⟨27083479372324750789655051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72222611659532668772413469 27083479372324750789655051)
  ·
    refine ⟨40625219058487126184482577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27083479372324750789655051 40625219058487126184482577)
    ·
      refine ⟨30468914293865344638361933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40625219058487126184482577 30468914293865344638361933)
      ·
        refine ⟨11425842860199504239385725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30468914293865344638361933 11425842860199504239385725)
        ·
          refine ⟨4284691072574814089769647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11425842860199504239385725 4284691072574814089769647)
          ·
            refine ⟨6427036608862221134654471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4284691072574814089769647 6427036608862221134654471)
            ·
              refine ⟨9640554913293331701981707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427036608862221134654471 9640554913293331701981707)
              ·
                refine ⟨14460832369939997552972561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9640554913293331701981707 14460832369939997552972561)
                ·
                  refine ⟨10845624277454998164729421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14460832369939997552972561 10845624277454998164729421)
                  ·
                    refine ⟨4067109104045624311773533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10845624277454998164729421 4067109104045624311773533)
                    ·
                      refine ⟨1525165914017109116915075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4067109104045624311773533 1525165914017109116915075)
                      ·
                        rfl

theorem cell23_2970250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 3, 1, 1, 1, 2, 3, 3].length) (baseStart_2970250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970250 prefixEnd_2970250 := by exact prefixLift 2970250
  have htrace : WordTrace (prefixWord ++ tailWord_2970250) baseStart_2970250 baseEnd_2970250 := by
    simpa [prefixWord, tailWord_2970250, baseEnd_2970250] using wordTrace_append hprefix tailTrace_2970250
  have hstable : (prefixWord ++ tailWord_2970250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970250).length < 2 ^ (prefixWord ++ tailWord_2970250).sum := by decide
  have hdescent : baseEnd_2970250 < baseStart_2970250 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970300 : List Nat := [2, 2, 2, 3, 1, 1, 4, 1, 3, 4]
def baseStart_2970300 : Nat := 118140960795 + 2970300 * 2 ^ 59
def prefixEnd_2970300 : Nat := 4983230072969 + 3 ^ 40 * 2970300 * 2
def baseEnd_2970300 : Nat := 508397196016611307096615

theorem tailTrace_2970300 : CollatzResearch.WordTrace tailWord_2970300 prefixEnd_2970300 508397196016611307096615 := by
  unfold tailWord_2970300
  simp only [CollatzResearch.WordTrace]
  refine ⟨54167870569558930848970177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72223827426078574465293569 54167870569558930848970177)
  ·
    refine ⟨40625902927169198136727633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54167870569558930848970177 40625902927169198136727633)
    ·
      refine ⟨30469427195376898602545725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40625902927169198136727633 30469427195376898602545725)
      ·
        refine ⟨11426035198266336975954647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30469427195376898602545725 11426035198266336975954647)
        ·
          refine ⟨17139052797399505463931971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11426035198266336975954647 17139052797399505463931971)
          ·
            refine ⟨25708579196099258195897957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17139052797399505463931971 25708579196099258195897957)
            ·
              refine ⟨4820358599268610911730867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25708579196099258195897957 4820358599268610911730867)
              ·
                refine ⟨7230537898902916367596301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820358599268610911730867 7230537898902916367596301)
                ·
                  refine ⟨2711451712088593637848613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7230537898902916367596301 2711451712088593637848613)
                  ·
                    refine ⟨508397196016611307096615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2711451712088593637848613 508397196016611307096615)
                    ·
                      rfl

theorem cell23_2970300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 4, 1, 3, 4].length) (baseStart_2970300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970300 prefixEnd_2970300 := by exact prefixLift 2970300
  have htrace : WordTrace (prefixWord ++ tailWord_2970300) baseStart_2970300 baseEnd_2970300 := by
    simpa [prefixWord, tailWord_2970300, baseEnd_2970300] using wordTrace_append hprefix tailTrace_2970300
  have hstable : (prefixWord ++ tailWord_2970300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970300).length < 2 ^ (prefixWord ++ tailWord_2970300).sum := by decide
  have hdescent : baseEnd_2970300 < baseStart_2970300 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970400 : List Nat := [2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5]
def baseStart_2970400 : Nat := 118140960795 + 2970400 * 2 ^ 59
def prefixEnd_2970400 : Nat := 4983230072969 + 3 ^ 40 * 2970400 * 2
def baseEnd_2970400 : Nat := 1525242936115283530039385

theorem tailTrace_2970400 : CollatzResearch.WordTrace tailWord_2970400 prefixEnd_2970400 1525242936115283530039385 := by
  unfold tailWord_2970400
  simp only [CollatzResearch.WordTrace]
  refine ⟨54169694219377789388290327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72226258959170385851053769 54169694219377789388290327)
  ·
    refine ⟨81254541329066684082435491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54169694219377789388290327 81254541329066684082435491)
    ·
      refine ⟨121881811993600026123653237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81254541329066684082435491 121881811993600026123653237)
      ·
        refine ⟨11426419874400002449092491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121881811993600026123653237 11426419874400002449092491)
        ·
          refine ⟨17139629811600003673638737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11426419874400002449092491 17139629811600003673638737)
          ·
            refine ⟨12854722358700002755229053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17139629811600003673638737 12854722358700002755229053)
            ·
              refine ⟨4820520884512501033210895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12854722358700002755229053 4820520884512501033210895)
              ·
                refine ⟨7230781326768751549816343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820520884512501033210895 7230781326768751549816343)
                ·
                  refine ⟨10846171990153127324724515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7230781326768751549816343 10846171990153127324724515)
                  ·
                    refine ⟨16269257985229690987086773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10846171990153127324724515 16269257985229690987086773)
                    ·
                      refine ⟨1525242936115283530039385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16269257985229690987086773 1525242936115283530039385)
                      ·
                        rfl

theorem cell23_2970400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 1, 1, 5].length) (baseStart_2970400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970400 prefixEnd_2970400 := by exact prefixLift 2970400
  have htrace : WordTrace (prefixWord ++ tailWord_2970400) baseStart_2970400 baseEnd_2970400 := by
    simpa [prefixWord, tailWord_2970400, baseEnd_2970400] using wordTrace_append hprefix tailTrace_2970400
  have hstable : (prefixWord ++ tailWord_2970400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970400).length < 2 ^ (prefixWord ++ tailWord_2970400).sum := by decide
  have hdescent : baseEnd_2970400 < baseStart_2970400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970463 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 4, 6]
def baseStart_2970463 : Nat := 118140960795 + 2970463 * 2 ^ 59
def prefixEnd_2970463 : Nat := 4983230072969 + 3 ^ 40 * 2970463 * 2
def baseEnd_2970463 : Nat := 508425095132172261183865

theorem tailTrace_2970463 : CollatzResearch.WordTrace tailWord_2970463 prefixEnd_2970463 508425095132172261183865 := by
  unfold tailWord_2970463
  simp only [CollatzResearch.WordTrace]
  refine ⟨108341686237527340536124043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72227790825018227024082695 108341686237527340536124043)
  ·
    refine ⟨162512529356291010804186065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108341686237527340536124043 162512529356291010804186065)
    ·
      refine ⟨121884397017218258103139549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162512529356291010804186065 121884397017218258103139549)
      ·
        refine ⟨45706648881456846788677331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121884397017218258103139549 45706648881456846788677331)
        ·
          refine ⟨68559973322185270183015997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45706648881456846788677331 68559973322185270183015997)
          ·
            refine ⟨25709989995819476318630999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68559973322185270183015997 25709989995819476318630999)
            ·
              refine ⟨38564984993729214477946499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25709989995819476318630999 38564984993729214477946499)
              ·
                refine ⟨57847477490593821716919749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38564984993729214477946499 57847477490593821716919749)
                ·
                  refine ⟨10846402029486341571922453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57847477490593821716919749 10846402029486341571922453)
                  ·
                    refine ⟨508425095132172261183865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10846402029486341571922453 508425095132172261183865)
                    ·
                      rfl

theorem cell23_2970463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 4, 6].length) (baseStart_2970463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970463 prefixEnd_2970463 := by exact prefixLift 2970463
  have htrace : WordTrace (prefixWord ++ tailWord_2970463) baseStart_2970463 baseEnd_2970463 := by
    simpa [prefixWord, tailWord_2970463, baseEnd_2970463] using wordTrace_append hprefix tailTrace_2970463
  have hstable : (prefixWord ++ tailWord_2970463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970463).length < 2 ^ (prefixWord ++ tailWord_2970463).sum := by decide
  have hdescent : baseEnd_2970463 < baseStart_2970463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970473 : List Nat := [1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 5]
def baseStart_2970473 : Nat := 118140960795 + 2970473 * 2 ^ 59
def prefixEnd_2970473 : Nat := 4983230072969 + 3 ^ 40 * 2970473 * 2
def baseEnd_2970473 : Nat := 1525280420203061744426549

theorem tailTrace_2970473 : CollatzResearch.WordTrace tailWord_2970473 prefixEnd_2970473 1525280420203061744426549 := by
  unfold tailWord_2970473
  simp only [CollatzResearch.WordTrace]
  refine ⟨108342050967491112243988073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72228033978327408162658715 108342050967491112243988073)
  ·
    refine ⟨81256538225618334182991055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108342050967491112243988073 81256538225618334182991055)
    ·
      refine ⟨121884807338427501274486583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81256538225618334182991055 121884807338427501274486583)
      ·
        refine ⟨182827211007641251911729875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121884807338427501274486583 182827211007641251911729875)
        ·
          refine ⟨274240816511461877867594813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182827211007641251911729875 274240816511461877867594813)
          ·
            refine ⟨102840306191798204200348055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274240816511461877867594813 102840306191798204200348055)
            ·
              refine ⟨154260459287697306300522083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102840306191798204200348055 154260459287697306300522083)
              ·
                refine ⟨231390688931545959450783125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154260459287697306300522083 231390688931545959450783125)
                ·
                  refine ⟨10846438543666216849255459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231390688931545959450783125 10846438543666216849255459)
                  ·
                    refine ⟨16269657815499325273883189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10846438543666216849255459 16269657815499325273883189)
                    ·
                      refine ⟨1525280420203061744426549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16269657815499325273883189 1525280420203061744426549)
                      ·
                        rfl

theorem cell23_2970473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 5].length) (baseStart_2970473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970473 prefixEnd_2970473 := by exact prefixLift 2970473
  have htrace : WordTrace (prefixWord ++ tailWord_2970473) baseStart_2970473 baseEnd_2970473 := by
    simpa [prefixWord, tailWord_2970473, baseEnd_2970473] using wordTrace_append hprefix tailTrace_2970473
  have hstable : (prefixWord ++ tailWord_2970473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970473).length < 2 ^ (prefixWord ++ tailWord_2970473).sum := by decide
  have hdescent : baseEnd_2970473 < baseStart_2970473 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970504 : List Nat := [2, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2]
def baseStart_2970504 : Nat := 118140960795 + 2970504 * 2 ^ 59
def prefixEnd_2970504 : Nat := 4983230072969 + 3 ^ 40 * 2970504 * 2
def baseEnd_2970504 : Nat := 1525296338103351123138907

theorem tailTrace_2970504 : CollatzResearch.WordTrace tailWord_2970504 prefixEnd_2970504 1525296338103351123138907 := by
  unfold tailWord_2970504
  simp only [CollatzResearch.WordTrace]
  refine ⟨54171590815189402269183283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72228787753585869692244377 54171590815189402269183283)
  ·
    refine ⟨81257386222784103403774925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54171590815189402269183283 81257386222784103403774925)
    ·
      refine ⟨30471519833544038776415597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81257386222784103403774925 30471519833544038776415597)
      ·
        refine ⟨11426819937579014541155849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30471519833544038776415597 11426819937579014541155849)
        ·
          refine ⟨8570114953184260905866887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11426819937579014541155849 8570114953184260905866887)
          ·
            refine ⟨12855172429776391358800331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8570114953184260905866887 12855172429776391358800331)
            ·
              refine ⟨19282758644664587038200497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12855172429776391358800331 19282758644664587038200497)
              ·
                refine ⟨14462068983498440278650373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19282758644664587038200497 14462068983498440278650373)
                ·
                  refine ⟨2711637934405957552246945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14462068983498440278650373 2711637934405957552246945)
                  ·
                    refine ⟨2033728450804468164185209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2711637934405957552246945 2033728450804468164185209)
                    ·
                      refine ⟨1525296338103351123138907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033728450804468164185209 1525296338103351123138907)
                      ·
                        rfl

theorem cell23_2970504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 2, 1, 1, 2, 4, 2, 2].length) (baseStart_2970504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970504 prefixEnd_2970504 := by exact prefixLift 2970504
  have htrace : WordTrace (prefixWord ++ tailWord_2970504) baseStart_2970504 baseEnd_2970504 := by
    simpa [prefixWord, tailWord_2970504, baseEnd_2970504] using wordTrace_append hprefix tailTrace_2970504
  have hstable : (prefixWord ++ tailWord_2970504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970504).length < 2 ^ (prefixWord ++ tailWord_2970504).sum := by decide
  have hdescent : baseEnd_2970504 < baseStart_2970504 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970527 : List Nat := [1, 1, 2, 5, 2, 3, 1, 1, 7]
def baseStart_2970527 : Nat := 118140960795 + 2970527 * 2 ^ 59
def prefixEnd_2970527 : Nat := 4983230072969 + 3 ^ 40 * 2970527 * 2
def baseEnd_2970527 : Nat := 169478683128711614794589

theorem tailTrace_2970527 : CollatzResearch.WordTrace tailWord_2970527 prefixEnd_2970527 169478683128711614794589 := by
  unfold tailWord_2970527
  simp only [CollatzResearch.WordTrace]
  refine ⟨108344020509295479466453835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72229347006196986310969223 108344020509295479466453835)
  ·
    refine ⟨162516030763943219199680753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108344020509295479466453835 162516030763943219199680753)
    ·
      refine ⟨121887023072957414399760565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162516030763943219199680753 121887023072957414399760565)
      ·
        refine ⟨11426908413089757599977553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121887023072957414399760565 11426908413089757599977553)
        ·
          refine ⟨8570181309817318199983165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11426908413089757599977553 8570181309817318199983165)
          ·
            refine ⟨3213817991181494324993687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8570181309817318199983165 3213817991181494324993687)
            ·
              refine ⟨4820726986772241487490531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213817991181494324993687 4820726986772241487490531)
              ·
                refine ⟨7231090480158362231235797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4820726986772241487490531 7231090480158362231235797)
                ·
                  refine ⟨169478683128711614794589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7231090480158362231235797 169478683128711614794589)
                  ·
                    rfl

theorem cell23_2970527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 7].length) (baseStart_2970527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970527 prefixEnd_2970527 := by exact prefixLift 2970527
  have htrace : WordTrace (prefixWord ++ tailWord_2970527) baseStart_2970527 baseEnd_2970527 := by
    simpa [prefixWord, tailWord_2970527, baseEnd_2970527] using wordTrace_append hprefix tailTrace_2970527
  have hstable : (prefixWord ++ tailWord_2970527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970527).length < 2 ^ (prefixWord ++ tailWord_2970527).sum := by decide
  have hdescent : baseEnd_2970527 < baseStart_2970527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970577 : List Nat := [1, 2, 2, 1, 2, 1, 4, 2, 2, 4, 2]
def baseStart_2970577 : Nat := 118140960795 + 2970577 * 2 ^ 59
def prefixEnd_2970577 : Nat := 4983230072969 + 3 ^ 40 * 2970577 * 2
def baseEnd_2970577 : Nat := 1525333822191129337526071

theorem tailTrace_2970577 : CollatzResearch.WordTrace tailWord_2970577 prefixEnd_2970577 1525333822191129337526071 := by
  unfold tailWord_2970577
  simp only [CollatzResearch.WordTrace]
  refine ⟨108345844159114338005773985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72230562772742892003849323 108345844159114338005773985)
  ·
    refine ⟨81259383119335753504330489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108345844159114338005773985 81259383119335753504330489)
    ·
      refine ⟨60944537339501815128247867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81259383119335753504330489 60944537339501815128247867)
      ·
        refine ⟨91416806009252722692371801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60944537339501815128247867 91416806009252722692371801)
        ·
          refine ⟨68562604506939542019278851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91416806009252722692371801 68562604506939542019278851)
          ·
            refine ⟨102843906760409313028918277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68562604506939542019278851 102843906760409313028918277)
            ·
              refine ⟨19283232517576746192922177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102843906760409313028918277 19283232517576746192922177)
              ·
                refine ⟨14462424388182559644691633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19283232517576746192922177 14462424388182559644691633)
                ·
                  refine ⟨10846818291136919733518725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14462424388182559644691633 10846818291136919733518725)
                  ·
                    refine ⟨2033778429588172450034761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10846818291136919733518725 2033778429588172450034761)
                    ·
                      refine ⟨1525333822191129337526071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033778429588172450034761 1525333822191129337526071)
                      ·
                        rfl

theorem cell23_2970577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 4, 2].length) (baseStart_2970577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970577 prefixEnd_2970577 := by exact prefixLift 2970577
  have htrace : WordTrace (prefixWord ++ tailWord_2970577) baseStart_2970577 baseEnd_2970577 := by
    simpa [prefixWord, tailWord_2970577, baseEnd_2970577] using wordTrace_append hprefix tailTrace_2970577
  have hstable : (prefixWord ++ tailWord_2970577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970577).length < 2 ^ (prefixWord ++ tailWord_2970577).sum := by decide
  have hdescent : baseEnd_2970577 < baseStart_2970577 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970614 : List Nat := [5, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3]
def baseStart_2970614 : Nat := 118140960795 + 2970614 * 2 ^ 59
def prefixEnd_2970614 : Nat := 4983230072969 + 3 ^ 40 * 2970614 * 2
def baseEnd_2970614 : Nat := 1525352820975345692763401

theorem tailTrace_2970614 : CollatzResearch.WordTrace tailWord_2970614 prefixEnd_2970614 1525352820975345692763401 := by
  unfold tailWord_2970614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6771699603748768332804431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72231462439986862216580597 6771699603748768332804431)
  ·
    refine ⟨10157549405623152499206647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6771699603748768332804431 10157549405623152499206647)
    ·
      refine ⟨15236324108434728748809971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10157549405623152499206647 15236324108434728748809971)
      ·
        refine ⟨22854486162652093123214957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15236324108434728748809971 22854486162652093123214957)
        ·
          refine ⟨8570432310994534921205609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22854486162652093123214957 8570432310994534921205609)
          ·
            refine ⟨6427824233245901190904207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8570432310994534921205609 6427824233245901190904207)
            ·
              refine ⟨9641736349868851786356311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6427824233245901190904207 9641736349868851786356311)
              ·
                refine ⟨14462604524803277679534467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9641736349868851786356311 14462604524803277679534467)
                ·
                  refine ⟨21693906787204916519301701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14462604524803277679534467 21693906787204916519301701)
                  ·
                    refine ⟨4067607522600921847369069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21693906787204916519301701 4067607522600921847369069)
                    ·
                      refine ⟨1525352820975345692763401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4067607522600921847369069 1525352820975345692763401)
                      ·
                        rfl

theorem cell23_2970614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3].length) (baseStart_2970614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970614 prefixEnd_2970614 := by exact prefixLift 2970614
  have htrace : WordTrace (prefixWord ++ tailWord_2970614) baseStart_2970614 baseEnd_2970614 := by
    simpa [prefixWord, tailWord_2970614, baseEnd_2970614] using wordTrace_append hprefix tailTrace_2970614
  have hstable : (prefixWord ++ tailWord_2970614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970614).length < 2 ^ (prefixWord ++ tailWord_2970614).sum := by decide
  have hdescent : baseEnd_2970614 < baseStart_2970614 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970634 : List Nat := [3, 1, 2, 2, 3, 3, 1, 2, 6]
def baseStart_2970634 : Nat := 118140960795 + 2970634 * 2 ^ 59
def prefixEnd_2970634 : Nat := 4983230072969 + 3 ^ 40 * 2970634 * 2
def baseEnd_2970634 : Nat := 169484787843159512723701

theorem tailTrace_2970634 : CollatzResearch.WordTrace tailWord_2970634 prefixEnd_2970634 169484787843159512723701 := by
  unfold tailWord_2970634
  simp only [CollatzResearch.WordTrace]
  refine ⟨27086980779976959185149739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72231948746605224493732637 27086980779976959185149739)
  ·
    refine ⟨40630471169965438777724609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27086980779976959185149739 40630471169965438777724609)
    ·
      refine ⟨30472853377474079083293457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40630471169965438777724609 30472853377474079083293457)
      ·
        refine ⟨22854640033105559312470093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30472853377474079083293457 22854640033105559312470093)
        ·
          refine ⟨8570490012414584742176285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22854640033105559312470093 8570490012414584742176285)
          ·
            refine ⟨3213933754655469278316107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8570490012414584742176285 3213933754655469278316107)
            ·
              refine ⟨4820900631983203917474161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3213933754655469278316107 4820900631983203917474161)
              ·
                refine ⟨3615675473987402938105621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4820900631983203917474161 3615675473987402938105621)
                ·
                  refine ⟨169484787843159512723701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3615675473987402938105621 169484787843159512723701)
                  ·
                    rfl

theorem cell23_2970634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 1, 2, 6].length) (baseStart_2970634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970634 prefixEnd_2970634 := by exact prefixLift 2970634
  have htrace : WordTrace (prefixWord ++ tailWord_2970634) baseStart_2970634 baseEnd_2970634 := by
    simpa [prefixWord, tailWord_2970634, baseEnd_2970634] using wordTrace_append hprefix tailTrace_2970634
  have hstable : (prefixWord ++ tailWord_2970634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970634).length < 2 ^ (prefixWord ++ tailWord_2970634).sum := by decide
  have hdescent : baseEnd_2970634 < baseStart_2970634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970667 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 2, 6, 2]
def baseStart_2970667 : Nat := 118140960795 + 2970667 * 2 ^ 59
def prefixEnd_2970667 : Nat := 4983230072969 + 3 ^ 40 * 2970667 * 2
def baseEnd_2970667 : Nat := 1525380035450033985400657

theorem tailTrace_2970667 : CollatzResearch.WordTrace tailWord_2970667 prefixEnd_2970667 1525380035450033985400657 := by
  unfold tailWord_2970667
  simp only [CollatzResearch.WordTrace]
  refine ⟨108349126728788283376550255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72232751152525522251033503 108349126728788283376550255)
  ·
    refine ⟨162523690093182425064825383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108349126728788283376550255 162523690093182425064825383)
    ·
      refine ⟨243785535139773637597238075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162523690093182425064825383 243785535139773637597238075)
      ·
        refine ⟨365678302709660456395857113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243785535139773637597238075 365678302709660456395857113)
        ·
          refine ⟨274258727032245342296892835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 365678302709660456395857113 274258727032245342296892835)
          ·
            refine ⟨411388090548368013445339253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274258727032245342296892835 411388090548368013445339253)
            ·
              refine ⟨38567633488909501260500555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411388090548368013445339253 38567633488909501260500555)
              ·
                refine ⟨57851450233364251890750833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38567633488909501260500555 57851450233364251890750833)
                ·
                  refine ⟨43388587675023188918063125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57851450233364251890750833 43388587675023188918063125)
                  ·
                    refine ⟨2033840047266711980534209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43388587675023188918063125 2033840047266711980534209)
                    ·
                      refine ⟨1525380035450033985400657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2033840047266711980534209 1525380035450033985400657)
                      ·
                        rfl

theorem cell23_2970667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 6, 2].length) (baseStart_2970667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970667 prefixEnd_2970667 := by exact prefixLift 2970667
  have htrace : WordTrace (prefixWord ++ tailWord_2970667) baseStart_2970667 baseEnd_2970667 := by
    simpa [prefixWord, tailWord_2970667, baseEnd_2970667] using wordTrace_append hprefix tailTrace_2970667
  have hstable : (prefixWord ++ tailWord_2970667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970667).length < 2 ^ (prefixWord ++ tailWord_2970667).sum := by decide
  have hdescent : baseEnd_2970667 < baseStart_2970667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970684 : List Nat := [2, 2, 2, 2, 2, 2, 2, 3, 1, 1, 4]
def baseStart_2970684 : Nat := 118140960795 + 2970684 * 2 ^ 59
def prefixEnd_2970684 : Nat := 4983230072969 + 3 ^ 40 * 2970684 * 2
def baseEnd_2970684 : Nat := 1525388764621160418888079

theorem tailTrace_2970684 : CollatzResearch.WordTrace tailWord_2970684 prefixEnd_2970684 1525388764621160418888079 := by
  unfold tailWord_2970684
  simp only [CollatzResearch.WordTrace]
  refine ⟨54174873384863347639959553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72233164513151130186612737 54174873384863347639959553)
  ·
    refine ⟨40631155038647510729969665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54174873384863347639959553 40631155038647510729969665)
    ·
      refine ⟨30473366278985633047477249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40631155038647510729969665 30473366278985633047477249)
      ·
        refine ⟨22855024709239224785607937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30473366278985633047477249 22855024709239224785607937)
        ·
          refine ⟨17141268531929418589205953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22855024709239224785607937 17141268531929418589205953)
          ·
            refine ⟨12855951398947063941904465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17141268531929418589205953 12855951398947063941904465)
            ·
              refine ⟨9641963549210297956428349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12855951398947063941904465 9641963549210297956428349)
              ·
                refine ⟨3615736330953861733660631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9641963549210297956428349 3615736330953861733660631)
                ·
                  refine ⟨5423604496430792600490947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3615736330953861733660631 5423604496430792600490947)
                  ·
                    refine ⟨8135406744646188900736421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423604496430792600490947 8135406744646188900736421)
                    ·
                      refine ⟨1525388764621160418888079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8135406744646188900736421 1525388764621160418888079)
                      ·
                        rfl

theorem cell23_2970684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 2, 3, 1, 1, 4].length) (baseStart_2970684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970684 prefixEnd_2970684 := by exact prefixLift 2970684
  have htrace : WordTrace (prefixWord ++ tailWord_2970684) baseStart_2970684 baseEnd_2970684 := by
    simpa [prefixWord, tailWord_2970684, baseEnd_2970684] using wordTrace_append hprefix tailTrace_2970684
  have hstable : (prefixWord ++ tailWord_2970684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970684).length < 2 ^ (prefixWord ++ tailWord_2970684).sum := by decide
  have hdescent : baseEnd_2970684 < baseStart_2970684 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970687 : List Nat := [1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3]
def baseStart_2970687 : Nat := 118140960795 + 2970687 * 2 ^ 59
def prefixEnd_2970687 : Nat := 4983230072969 + 3 ^ 40 * 2970687 * 2
def baseEnd_2970687 : Nat := 1525390305063123907150565

theorem tailTrace_2970687 : CollatzResearch.WordTrace tailWord_2970687 prefixEnd_2970687 1525390305063123907150565 := by
  unfold tailWord_2970687
  simp only [CollatzResearch.WordTrace]
  refine ⟨108349856188715826792278315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72233237459143884528185543 108349856188715826792278315)
  ·
    refine ⟨162524784283073740188417473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108349856188715826792278315 162524784283073740188417473)
    ·
      refine ⟨121893588212305305141313105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162524784283073740188417473 121893588212305305141313105)
      ·
        refine ⟨91420191159228978855984829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121893588212305305141313105 91420191159228978855984829)
        ·
          refine ⟨34282571684710867070994311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91420191159228978855984829 34282571684710867070994311)
          ·
            refine ⟨51423857527066300606491467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34282571684710867070994311 51423857527066300606491467)
            ·
              refine ⟨77135786290599450909737201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51423857527066300606491467 77135786290599450909737201)
              ·
                refine ⟨57851839717949588182302901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77135786290599450909737201 57851839717949588182302901)
                ·
                  refine ⟨5423609973557773892090897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57851839717949588182302901 5423609973557773892090897)
                  ·
                    refine ⟨4067707480168330419068173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5423609973557773892090897 4067707480168330419068173)
                    ·
                      refine ⟨1525390305063123907150565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4067707480168330419068173 1525390305063123907150565)
                      ·
                        rfl

theorem cell23_2970687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 3].length) (baseStart_2970687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970687 prefixEnd_2970687 := by exact prefixLift 2970687
  have htrace : WordTrace (prefixWord ++ tailWord_2970687) baseStart_2970687 baseEnd_2970687 := by
    simpa [prefixWord, tailWord_2970687, baseEnd_2970687] using wordTrace_append hprefix tailTrace_2970687
  have hstable : (prefixWord ++ tailWord_2970687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970687).length < 2 ^ (prefixWord ++ tailWord_2970687).sum := by decide
  have hdescent : baseEnd_2970687 < baseStart_2970687 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970718 : List Nat := [4, 4, 1, 1, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2970718 : Nat := 118140960795 + 2970718 * 2 ^ 59
def prefixEnd_2970718 : Nat := 4983230072969 + 3 ^ 40 * 2970718 * 2
def baseEnd_2970718 : Nat := 1525406222963413285862923

theorem tailTrace_2970718 : CollatzResearch.WordTrace tailWord_2970718 prefixEnd_2970718 1525406222963413285862923 := by
  unfold tailWord_2970718
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543873356450439885832101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72233991234402346057771205 13543873356450439885832101)
  ·
    refine ⟨2539476254334457478593519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13543873356450439885832101 2539476254334457478593519)
    ·
      refine ⟨3809214381501686217890279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2539476254334457478593519 3809214381501686217890279)
      ·
        refine ⟨5713821572252529326835419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3809214381501686217890279 5713821572252529326835419)
        ·
          refine ⟨8570732358378793990253129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5713821572252529326835419 8570732358378793990253129)
          ·
            refine ⟨6428049268784095492689847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8570732358378793990253129 6428049268784095492689847)
            ·
              refine ⟨9642073903176143239034771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428049268784095492689847 9642073903176143239034771)
              ·
                refine ⟨14463110854764214858552157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642073903176143239034771 14463110854764214858552157)
                ·
                  refine ⟨5423666570536580571957059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14463110854764214858552157 5423666570536580571957059)
                  ·
                    refine ⟨8135499855804870857935589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5423666570536580571957059 8135499855804870857935589)
                    ·
                      refine ⟨1525406222963413285862923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8135499855804870857935589 1525406222963413285862923)
                      ·
                        rfl

theorem cell23_2970718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2970718 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970718 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970718 prefixEnd_2970718 := by exact prefixLift 2970718
  have htrace : WordTrace (prefixWord ++ tailWord_2970718) baseStart_2970718 baseEnd_2970718 := by
    simpa [prefixWord, tailWord_2970718, baseEnd_2970718] using wordTrace_append hprefix tailTrace_2970718
  have hstable : (prefixWord ++ tailWord_2970718).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970718).length < 2 ^ (prefixWord ++ tailWord_2970718).sum := by decide
  have hdescent : baseEnd_2970718 < baseStart_2970718 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970734 : List Nat := [4, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3]
def baseStart_2970734 : Nat := 118140960795 + 2970734 * 2 ^ 59
def prefixEnd_2970734 : Nat := 4983230072969 + 3 ^ 40 * 2970734 * 2
def baseEnd_2970734 : Nat := 1525414438653885223262849

theorem tailTrace_2970734 : CollatzResearch.WordTrace tailWord_2970734 prefixEnd_2970734 1525414438653885223262849 := by
  unfold tailWord_2970734
  simp only [CollatzResearch.WordTrace]
  refine ⟨13543946302443194227404907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72234380279697035879492837 13543946302443194227404907)
  ·
    refine ⟨20315919453664791341107361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13543946302443194227404907 20315919453664791341107361)
    ·
      refine ⟨15236939590248593505830521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20315919453664791341107361 15236939590248593505830521)
      ·
        refine ⟨11427704692686445129372891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15236939590248593505830521 11427704692686445129372891)
        ·
          refine ⟨17141557039029667694059337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11427704692686445129372891 17141557039029667694059337)
          ·
            refine ⟨12856167779272250770544503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17141557039029667694059337 12856167779272250770544503)
            ·
              refine ⟨19284251668908376155816755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12856167779272250770544503 19284251668908376155816755)
              ·
                refine ⟨28926377503362564233725133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19284251668908376155816755 28926377503362564233725133)
                ·
                  refine ⟨10847391563760961587646925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28926377503362564233725133 10847391563760961587646925)
                  ·
                    refine ⟨4067771836410360595367597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10847391563760961587646925 4067771836410360595367597)
                    ·
                      refine ⟨1525414438653885223262849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4067771836410360595367597 1525414438653885223262849)
                      ·
                        rfl

theorem cell23_2970734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 1, 3, 3, 3].length) (baseStart_2970734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970734 prefixEnd_2970734 := by exact prefixLift 2970734
  have htrace : WordTrace (prefixWord ++ tailWord_2970734) baseStart_2970734 baseEnd_2970734 := by
    simpa [prefixWord, tailWord_2970734, baseEnd_2970734] using wordTrace_append hprefix tailTrace_2970734
  have hstable : (prefixWord ++ tailWord_2970734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970734).length < 2 ^ (prefixWord ++ tailWord_2970734).sum := by decide
  have hdescent : baseEnd_2970734 < baseStart_2970734 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970814 : List Nat := [4, 2, 1, 1, 3, 1, 1, 3, 7]
def baseStart_2970814 : Nat := 118140960795 + 2970814 * 2 ^ 59
def prefixEnd_2970814 : Nat := 4983230072969 + 3 ^ 40 * 2970814 * 2
def baseEnd_2970814 : Nat := 169495057456249434473609

theorem tailTrace_2970814 : CollatzResearch.WordTrace tailWord_2970814 prefixEnd_2970814 169495057456249434473609 := by
  unfold tailWord_2970814
  simp only [CollatzResearch.WordTrace]
  refine ⟨13544311032406965935268937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72236325506170484988100997 13544311032406965935268937)
  ·
    refine ⟨10158233274305224451451703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13544311032406965935268937 10158233274305224451451703)
    ·
      refine ⟨15237349911457836677177555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158233274305224451451703 15237349911457836677177555)
      ·
        refine ⟨22856024867186755015766333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15237349911457836677177555 22856024867186755015766333)
        ·
          refine ⟨8571009325195033130912375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22856024867186755015766333 8571009325195033130912375)
          ·
            refine ⟨12856513987792549696368563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8571009325195033130912375 12856513987792549696368563)
            ·
              refine ⟨19284770981688824544552845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12856513987792549696368563 19284770981688824544552845)
              ·
                refine ⟨7231789118133309204207317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19284770981688824544552845 7231789118133309204207317)
                ·
                  refine ⟨169495057456249434473609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7231789118133309204207317 169495057456249434473609)
                  ·
                    rfl

theorem cell23_2970814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 1, 3, 7].length) (baseStart_2970814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970814 prefixEnd_2970814 := by exact prefixLift 2970814
  have htrace : WordTrace (prefixWord ++ tailWord_2970814) baseStart_2970814 baseEnd_2970814 := by
    simpa [prefixWord, tailWord_2970814, baseEnd_2970814] using wordTrace_append hprefix tailTrace_2970814
  have hstable : (prefixWord ++ tailWord_2970814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970814).length < 2 ^ (prefixWord ++ tailWord_2970814).sum := by decide
  have hdescent : baseEnd_2970814 < baseStart_2970814 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970824 : List Nat := [2, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3]
def baseStart_2970824 : Nat := 118140960795 + 2970824 * 2 ^ 59
def prefixEnd_2970824 : Nat := 4983230072969 + 3 ^ 40 * 2970824 * 2
def baseEnd_2970824 : Nat := 1525460651912789871137435

theorem tailTrace_2970824 : CollatzResearch.WordTrace tailWord_2970824 prefixEnd_2970824 1525460651912789871137435 := by
  unfold tailWord_2970824
  simp only [CollatzResearch.WordTrace]
  refine ⟨54177426494609749595007763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72236568659479666126677017 54177426494609749595007763)
  ·
    refine ⟨81266139741914624392511645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54177426494609749595007763 81266139741914624392511645)
    ·
      refine ⟨30474802403217984147191867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81266139741914624392511645 30474802403217984147191867)
      ·
        refine ⟨45712203604826976220787801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30474802403217984147191867 45712203604826976220787801)
        ·
          refine ⟨34284152703620232165590851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45712203604826976220787801 34284152703620232165590851)
          ·
            refine ⟨51426229055430348248386277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34284152703620232165590851 51426229055430348248386277)
            ·
              refine ⟨9642417947893190296572427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51426229055430348248386277 9642417947893190296572427)
              ·
                refine ⟨14463626921839785444858641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642417947893190296572427 14463626921839785444858641)
                ·
                  refine ⟨10847720191379839083643981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14463626921839785444858641 10847720191379839083643981)
                  ·
                    refine ⟨4067895071767439656366493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10847720191379839083643981 4067895071767439656366493)
                    ·
                      refine ⟨1525460651912789871137435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4067895071767439656366493 1525460651912789871137435)
                      ·
                        rfl

theorem cell23_2970824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 4, 1, 2, 3, 3].length) (baseStart_2970824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970824 prefixEnd_2970824 := by exact prefixLift 2970824
  have htrace : WordTrace (prefixWord ++ tailWord_2970824) baseStart_2970824 baseEnd_2970824 := by
    simpa [prefixWord, tailWord_2970824, baseEnd_2970824] using wordTrace_append hprefix tailTrace_2970824
  have hstable : (prefixWord ++ tailWord_2970824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970824).length < 2 ^ (prefixWord ++ tailWord_2970824).sum := by decide
  have hdescent : baseEnd_2970824 < baseStart_2970824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970827 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 6, 5]
def baseStart_2970827 : Nat := 118140960795 + 2970827 * 2 ^ 59
def prefixEnd_2970827 : Nat := 4983230072969 + 3 ^ 40 * 2970827 * 2
def baseEnd_2970827 : Nat := 508487397451584453133307

theorem tailTrace_2970827 : CollatzResearch.WordTrace tailWord_2970827 prefixEnd_2970827 508487397451584453133307 := by
  unfold tailWord_2970827
  simp only [CollatzResearch.WordTrace]
  refine ⟨108354962408208630702374735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72236641605472420468249823 108354962408208630702374735)
  ·
    refine ⟨162532443612312946053562103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108354962408208630702374735 162532443612312946053562103)
    ·
      refine ⟨243798665418469419080343155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162532443612312946053562103 243798665418469419080343155)
      ·
        refine ⟨365697998127704128620514733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243798665418469419080343155 365697998127704128620514733)
        ·
          refine ⟨137136749297889048232693025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 365697998127704128620514733 137136749297889048232693025)
          ·
            refine ⟨102852561973416786174519769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137136749297889048232693025 102852561973416786174519769)
            ·
              refine ⟨77139421480062589630889827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102852561973416786174519769 77139421480062589630889827)
              ·
                refine ⟨115709132220093884446334741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77139421480062589630889827 115709132220093884446334741)
                ·
                  refine ⟨5423865572816900833421941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115709132220093884446334741 5423865572816900833421941)
                  ·
                    refine ⟨508487397451584453133307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5423865572816900833421941 508487397451584453133307)
                    ·
                      rfl

theorem cell23_2970827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 5].length) (baseStart_2970827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970827 prefixEnd_2970827 := by exact prefixLift 2970827
  have htrace : WordTrace (prefixWord ++ tailWord_2970827) baseStart_2970827 baseEnd_2970827 := by
    simpa [prefixWord, tailWord_2970827, baseEnd_2970827] using wordTrace_append hprefix tailTrace_2970827
  have hstable : (prefixWord ++ tailWord_2970827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970827).length < 2 ^ (prefixWord ++ tailWord_2970827).sum := by decide
  have hdescent : baseEnd_2970827 < baseStart_2970827 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970861 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 2, 5]
def baseStart_2970861 : Nat := 118140960795 + 2970861 * 2 ^ 59
def prefixEnd_2970861 : Nat := 4983230072969 + 3 ^ 40 * 2970861 * 2
def baseEnd_2970861 : Nat := 508493216899002075458255

theorem tailTrace_2970861 : CollatzResearch.WordTrace tailWord_2970861 prefixEnd_2970861 508493216899002075458255 := by
  unfold tailWord_2970861
  simp only [CollatzResearch.WordTrace]
  refine ⟨108356202490085454509112437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72237468326723636339408291 108356202490085454509112437)
  ·
    refine ⟨10158393983445511360229291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108356202490085454509112437 10158393983445511360229291)
    ·
      refine ⟨15237590975168267040343937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10158393983445511360229291 15237590975168267040343937)
      ·
        refine ⟨11428193231376200280257953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15237590975168267040343937 11428193231376200280257953)
        ·
          refine ⟨8571144923532150210193465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11428193231376200280257953 8571144923532150210193465)
          ·
            refine ⟨6428358692649112657645099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8571144923532150210193465 6428358692649112657645099)
            ·
              refine ⟨9642538038973668986467649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428358692649112657645099 9642538038973668986467649)
              ·
                refine ⟨7231903529230251739850737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9642538038973668986467649 7231903529230251739850737)
                ·
                  refine ⟨5423927646922688804888053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7231903529230251739850737 5423927646922688804888053)
                  ·
                    refine ⟨508493216899002075458255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5423927646922688804888053 508493216899002075458255)
                    ·
                      rfl

theorem cell23_2970861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 5].length) (baseStart_2970861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970861 prefixEnd_2970861 := by exact prefixLift 2970861
  have htrace : WordTrace (prefixWord ++ tailWord_2970861) baseStart_2970861 baseEnd_2970861 := by
    simpa [prefixWord, tailWord_2970861, baseEnd_2970861] using wordTrace_append hprefix tailTrace_2970861
  have hstable : (prefixWord ++ tailWord_2970861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970861).length < 2 ^ (prefixWord ++ tailWord_2970861).sum := by decide
  have hdescent : baseEnd_2970861 < baseStart_2970861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970907 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8]
def baseStart_2970907 : Nat := 118140960795 + 2970907 * 2 ^ 59
def prefixEnd_2970907 : Nat := 4983230072969 + 3 ^ 40 * 2970907 * 2
def baseEnd_2970907 : Nat := 1525503270807113046399553

theorem tailTrace_2970907 : CollatzResearch.WordTrace tailWord_2970907 prefixEnd_2970907 1525503270807113046399553 := by
  unfold tailWord_2970907
  simp only [CollatzResearch.WordTrace]
  refine ⟨108357880247918804365286975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72238586831945869576857983 108357880247918804365286975)
  ·
    refine ⟨162536820371878206547930463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108357880247918804365286975 162536820371878206547930463)
    ·
      refine ⟨243805230557817309821895695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162536820371878206547930463 243805230557817309821895695)
      ·
        refine ⟨365707845836725964732843543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243805230557817309821895695 365707845836725964732843543)
        ·
          refine ⟨548561768755088947099265315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 365707845836725964732843543 548561768755088947099265315)
          ·
            refine ⟨822842653132633420648897973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 548561768755088947099265315 822842653132633420648897973)
            ·
              refine ⟨77141498731184383185834185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 822842653132633420648897973 77141498731184383185834185)
              ·
                refine ⟨57856124048388287389375639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77141498731184383185834185 57856124048388287389375639)
                ·
                  refine ⟨86784186072582431084063459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57856124048388287389375639 86784186072582431084063459)
                  ·
                    refine ⟨130176279108873646626095189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 86784186072582431084063459 130176279108873646626095189)
                    ·
                      refine ⟨1525503270807113046399553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 130176279108873646626095189 1525503270807113046399553)
                      ·
                        rfl

theorem cell23_2970907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 8].length) (baseStart_2970907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970907 prefixEnd_2970907 := by exact prefixLift 2970907
  have htrace : WordTrace (prefixWord ++ tailWord_2970907) baseStart_2970907 baseEnd_2970907 := by
    simpa [prefixWord, tailWord_2970907, baseEnd_2970907] using wordTrace_append hprefix tailTrace_2970907
  have hstable : (prefixWord ++ tailWord_2970907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970907).length < 2 ^ (prefixWord ++ tailWord_2970907).sum := by decide
  have hdescent : baseEnd_2970907 < baseStart_2970907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970965 : List Nat := [1, 3, 2, 2, 3, 1, 1, 5, 1, 1, 3]
def baseStart_2970965 : Nat := 118140960795 + 2970965 * 2 ^ 59
def prefixEnd_2970965 : Nat := 4983230072969 + 3 ^ 40 * 2970965 * 2
def baseEnd_2970965 : Nat := 1525533052685073819474287

theorem tailTrace_2970965 : CollatzResearch.WordTrace tailWord_2970965 prefixEnd_2970965 1525533052685073819474287 := by
  unfold tailWord_2970965
  simp only [CollatzResearch.WordTrace]
  refine ⟨108359995681708680270898349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72239997121139120180598899 108359995681708680270898349)
  ·
    refine ⟨40634998380640755101586881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108359995681708680270898349 40634998380640755101586881)
    ·
      refine ⟨30476248785480566326190161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40634998380640755101586881 30476248785480566326190161)
      ·
        refine ⟨22857186589110424744642621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30476248785480566326190161 22857186589110424744642621)
        ·
          refine ⟨8571444970916409279240983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22857186589110424744642621 8571444970916409279240983)
          ·
            refine ⟨12857167456374613918861475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8571444970916409279240983 12857167456374613918861475)
            ·
              refine ⟨19285751184561920878292213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12857167456374613918861475 19285751184561920878292213)
              ·
                refine ⟨1808039173552680082339895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19285751184561920878292213 1808039173552680082339895)
                ·
                  refine ⟨2712058760329020123509843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808039173552680082339895 2712058760329020123509843)
                  ·
                    refine ⟨4068088140493530185264765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2712058760329020123509843 4068088140493530185264765)
                    ·
                      refine ⟨1525533052685073819474287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4068088140493530185264765 1525533052685073819474287)
                      ·
                        rfl

theorem cell23_2970965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 1, 5, 1, 1, 3].length) (baseStart_2970965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970965 prefixEnd_2970965 := by exact prefixLift 2970965
  have htrace : WordTrace (prefixWord ++ tailWord_2970965) baseStart_2970965 baseEnd_2970965 := by
    simpa [prefixWord, tailWord_2970965, baseEnd_2970965] using wordTrace_append hprefix tailTrace_2970965
  have hstable : (prefixWord ++ tailWord_2970965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970965).length < 2 ^ (prefixWord ++ tailWord_2970965).sum := by decide
  have hdescent : baseEnd_2970965 < baseStart_2970965 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970981 : List Nat := [1, 3, 1, 3, 1, 2, 3, 1, 4, 4]
def baseStart_2970981 : Nat := 118140960795 + 2970981 * 2 ^ 59
def prefixEnd_2970981 : Nat := 4983230072969 + 3 ^ 40 * 2970981 * 2
def baseEnd_2970981 : Nat := 508513756125181918958071

theorem tailTrace_2970981 : CollatzResearch.WordTrace tailWord_2970981 prefixEnd_2970981 508513756125181918958071 := by
  unfold tailWord_2970981
  simp only [CollatzResearch.WordTrace]
  refine ⟨108360579249650715003480797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72240386166433810002320531 108360579249650715003480797)
  ·
    refine ⟨40635217218619018126305299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108360579249650715003480797 40635217218619018126305299)
    ·
      refine ⟨60952825827928527189457949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40635217218619018126305299 60952825827928527189457949)
      ·
        refine ⟨22857309685473197696046731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60952825827928527189457949 22857309685473197696046731)
        ·
          refine ⟨34285964528209796544070097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22857309685473197696046731 34285964528209796544070097)
          ·
            refine ⟨25714473396157347408052573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34285964528209796544070097 25714473396157347408052573)
            ·
              refine ⟨9642927523559005278019715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25714473396157347408052573 9642927523559005278019715)
              ·
                refine ⟨14464391285338507917029573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9642927523559005278019715 14464391285338507917029573)
                ·
                  refine ⟨2712073366000970234443045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14464391285338507917029573 2712073366000970234443045)
                  ·
                    refine ⟨508513756125181918958071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2712073366000970234443045 508513756125181918958071)
                    ·
                      rfl

theorem cell23_2970981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 4].length) (baseStart_2970981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970981 prefixEnd_2970981 := by exact prefixLift 2970981
  have htrace : WordTrace (prefixWord ++ tailWord_2970981) baseStart_2970981 baseEnd_2970981 := by
    simpa [prefixWord, tailWord_2970981, baseEnd_2970981] using wordTrace_append hprefix tailTrace_2970981
  have hstable : (prefixWord ++ tailWord_2970981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970981).length < 2 ^ (prefixWord ++ tailWord_2970981).sum := by decide
  have hdescent : baseEnd_2970981 < baseStart_2970981 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2970994 : List Nat := [3, 2, 1, 2, 1, 2, 2, 10]
def baseStart_2970994 : Nat := 118140960795 + 2970994 * 2 ^ 59
def prefixEnd_2970994 : Nat := 4983230072969 + 3 ^ 40 * 2970994 * 2
def baseEnd_2970994 : Nat := 56501775689779785407839

theorem tailTrace_2970994 : CollatzResearch.WordTrace tailWord_2970994 prefixEnd_2970994 56501775689779785407839 := by
  unfold tailWord_2970994
  simp only [CollatzResearch.WordTrace]
  refine ⟨27090263349650904555926009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72240702265735745482469357 27090263349650904555926009)
  ·
    refine ⟨20317697512238178416944507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27090263349650904555926009 20317697512238178416944507)
    ·
      refine ⟨30476546268357267625416761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20317697512238178416944507 30476546268357267625416761)
      ·
        refine ⟨22857409701267950719062571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30476546268357267625416761 22857409701267950719062571)
        ·
          refine ⟨34286114551901926078593857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22857409701267950719062571 34286114551901926078593857)
          ·
            refine ⟨25714585913926444558945393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34286114551901926078593857 25714585913926444558945393)
            ·
              refine ⟨19285939435444833419209045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25714585913926444558945393 19285939435444833419209045)
              ·
                refine ⟨56501775689779785407839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19285939435444833419209045 56501775689779785407839)
                ·
                  rfl

theorem cell23_2970994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 10].length) (baseStart_2970994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2970994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2970994 prefixEnd_2970994 := by exact prefixLift 2970994
  have htrace : WordTrace (prefixWord ++ tailWord_2970994) baseStart_2970994 baseEnd_2970994 := by
    simpa [prefixWord, tailWord_2970994, baseEnd_2970994] using wordTrace_append hprefix tailTrace_2970994
  have hstable : (prefixWord ++ tailWord_2970994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2970994).length < 2 ^ (prefixWord ++ tailWord_2970994).sum := by decide
  have hdescent : baseEnd_2970994 < baseStart_2970994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2970994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971001 : List Nat := [1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 4]
def baseStart_2971001 : Nat := 118140960795 + 2971001 * 2 ^ 59
def prefixEnd_2971001 : Nat := 4983230072969 + 3 ^ 40 * 2971001 * 2
def baseEnd_2971001 : Nat := 1525551537988635678624121

theorem tailTrace_2971001 : CollatzResearch.WordTrace tailWord_2971001 prefixEnd_2971001 1525551537988635678624121 := by
  unfold tailWord_2971001
  simp only [CollatzResearch.WordTrace]
  refine ⟨108361308709578258419208857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72240872473052172279472571 108361308709578258419208857)
  ·
    refine ⟨81270981532183693814406643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108361308709578258419208857 81270981532183693814406643)
    ·
      refine ⟨121906472298275540721609965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81270981532183693814406643 121906472298275540721609965)
      ·
        refine ⟨45714927111853327770603737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121906472298275540721609965 45714927111853327770603737)
        ·
          refine ⟨34286195333889995827952803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45714927111853327770603737 34286195333889995827952803)
          ·
            refine ⟨51429293000834993741929205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34286195333889995827952803 51429293000834993741929205)
            ·
              refine ⟨4821496218828280663305863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51429293000834993741929205 4821496218828280663305863)
              ·
                refine ⟨7232244328242420994958795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4821496218828280663305863 7232244328242420994958795)
                ·
                  refine ⟨10848366492363631492438193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7232244328242420994958795 10848366492363631492438193)
                  ·
                    refine ⟨8136274869272723619328645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10848366492363631492438193 8136274869272723619328645)
                    ·
                      refine ⟨1525551537988635678624121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8136274869272723619328645 1525551537988635678624121)
                      ·
                        rfl

theorem cell23_2971001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 4].length) (baseStart_2971001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971001 prefixEnd_2971001 := by exact prefixLift 2971001
  have htrace : WordTrace (prefixWord ++ tailWord_2971001) baseStart_2971001 baseEnd_2971001 := by
    simpa [prefixWord, tailWord_2971001, baseEnd_2971001] using wordTrace_append hprefix tailTrace_2971001
  have hstable : (prefixWord ++ tailWord_2971001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971001).length < 2 ^ (prefixWord ++ tailWord_2971001).sum := by decide
  have hdescent : baseEnd_2971001 < baseStart_2971001 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971011 : List Nat := [1, 1, 1, 3, 5, 1, 4, 7]
def baseStart_2971011 : Nat := 118140960795 + 2971011 * 2 ^ 59
def prefixEnd_2971011 : Nat := 4983230072969 + 3 ^ 40 * 2971011 * 2
def baseEnd_2971011 : Nat := 56502098992414097759225

theorem tailTrace_2971011 : CollatzResearch.WordTrace tailWord_2971011 prefixEnd_2971011 56502098992414097759225 := by
  unfold tailWord_2971011
  simp only [CollatzResearch.WordTrace]
  refine ⟨108361673439542030127072887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72241115626361353418048591 108361673439542030127072887)
  ·
    refine ⟨162542510159313045190609331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108361673439542030127072887 162542510159313045190609331)
    ·
      refine ⟨243813765238969567785913997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162542510159313045190609331 243813765238969567785913997)
      ·
        refine ⟨91430161964613587919717749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243813765238969567785913997 91430161964613587919717749)
        ·
          refine ⟨8571577684182523867473539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 91430161964613587919717749 8571577684182523867473539)
          ·
            refine ⟨12857366526273785801210309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8571577684182523867473539 12857366526273785801210309)
            ·
              refine ⟨2410756223676334837726933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12857366526273785801210309 2410756223676334837726933)
              ·
                refine ⟨56502098992414097759225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2410756223676334837726933 56502098992414097759225)
                ·
                  rfl

theorem cell23_2971011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 7].length) (baseStart_2971011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971011 prefixEnd_2971011 := by exact prefixLift 2971011
  have htrace : WordTrace (prefixWord ++ tailWord_2971011) baseStart_2971011 baseEnd_2971011 := by
    simpa [prefixWord, tailWord_2971011, baseEnd_2971011] using wordTrace_append hprefix tailTrace_2971011
  have hstable : (prefixWord ++ tailWord_2971011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971011).length < 2 ^ (prefixWord ++ tailWord_2971011).sum := by decide
  have hdescent : baseEnd_2971011 < baseStart_2971011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971039 : List Nat := [1, 1, 2, 5, 1, 3, 3, 2, 1, 2, 2]
def baseStart_2971039 : Nat := 118140960795 + 2971039 * 2 ^ 59
def prefixEnd_2971039 : Nat := 4983230072969 + 3 ^ 40 * 2971039 * 2
def baseEnd_2971039 : Nat := 1525571050253506529948947

theorem tailTrace_2971039 : CollatzResearch.WordTrace tailWord_2971039 prefixEnd_2971039 1525571050253506529948947 := by
  unfold tailWord_2971039
  simp only [CollatzResearch.WordTrace]
  refine ⟨108362694683440590909092171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72241796455627060606061447 108362694683440590909092171)
  ·
    refine ⟨162544042025160886363638257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108362694683440590909092171 162544042025160886363638257)
    ·
      refine ⟨121908031518870664772728693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162544042025160886363638257 121908031518870664772728693)
      ·
        refine ⟨11428877954894124822443315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121908031518870664772728693 11428877954894124822443315)
        ·
          refine ⟨17143316932341187233664973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11428877954894124822443315 17143316932341187233664973)
          ·
            refine ⟨6428743849627945212624365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17143316932341187233664973 6428743849627945212624365)
            ·
              refine ⟨2410778943610479454734137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6428743849627945212624365 2410778943610479454734137)
              ·
                refine ⟨1808084207707859591050603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2410778943610479454734137 1808084207707859591050603)
                ·
                  refine ⟨2712126311561789386575905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808084207707859591050603 2712126311561789386575905)
                  ·
                    refine ⟨2034094733671342039931929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712126311561789386575905 2034094733671342039931929)
                    ·
                      refine ⟨1525571050253506529948947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034094733671342039931929 1525571050253506529948947)
                      ·
                        rfl

theorem cell23_2971039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 2, 2].length) (baseStart_2971039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971039 prefixEnd_2971039 := by exact prefixLift 2971039
  have htrace : WordTrace (prefixWord ++ tailWord_2971039) baseStart_2971039 baseEnd_2971039 := by
    simpa [prefixWord, tailWord_2971039, baseEnd_2971039] using wordTrace_append hprefix tailTrace_2971039
  have hstable : (prefixWord ++ tailWord_2971039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971039).length < 2 ^ (prefixWord ++ tailWord_2971039).sum := by decide
  have hdescent : baseEnd_2971039 < baseStart_2971039 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971065 : List Nat := [1, 2, 1, 4, 4, 1, 1, 1, 3, 3, 2]
def baseStart_2971065 : Nat := 118140960795 + 2971065 * 2 ^ 59
def prefixEnd_2971065 : Nat := 4983230072969 + 3 ^ 40 * 2971065 * 2
def baseEnd_2971065 : Nat := 1525584400750523428223827

theorem tailTrace_2971065 : CollatzResearch.WordTrace tailWord_2971065 prefixEnd_2971065 1525584400750523428223827 := by
  unfold tailWord_2971065
  simp only [CollatzResearch.WordTrace]
  refine ⟨108363642981346397349538649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72242428654230931566359099 108363642981346397349538649)
  ·
    refine ⟨81272732236009798012153987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108363642981346397349538649 81272732236009798012153987)
    ·
      refine ⟨121909098354014697018230981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81272732236009798012153987 121909098354014697018230981)
      ·
        refine ⟨22857955941377755690918309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121909098354014697018230981 22857955941377755690918309)
        ·
          refine ⟨4285866739008329192047183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22857955941377755690918309 4285866739008329192047183)
          ·
            refine ⟨6428800108512493788070775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4285866739008329192047183 6428800108512493788070775)
            ·
              refine ⟨9643200162768740682106163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6428800108512493788070775 9643200162768740682106163)
              ·
                refine ⟨14464800244153111023159245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9643200162768740682106163 14464800244153111023159245)
                ·
                  refine ⟨5424300091557416633684717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14464800244153111023159245 5424300091557416633684717)
                  ·
                    refine ⟨2034112534334031237631769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5424300091557416633684717 2034112534334031237631769)
                    ·
                      refine ⟨1525584400750523428223827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034112534334031237631769 1525584400750523428223827)
                      ·
                        rfl

theorem cell23_2971065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 3, 2].length) (baseStart_2971065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971065 prefixEnd_2971065 := by exact prefixLift 2971065
  have htrace : WordTrace (prefixWord ++ tailWord_2971065) baseStart_2971065 baseEnd_2971065 := by
    simpa [prefixWord, tailWord_2971065, baseEnd_2971065] using wordTrace_append hprefix tailTrace_2971065
  have hstable : (prefixWord ++ tailWord_2971065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971065).length < 2 ^ (prefixWord ++ tailWord_2971065).sum := by decide
  have hdescent : baseEnd_2971065 < baseStart_2971065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971082 : List Nat := [3, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2]
def baseStart_2971082 : Nat := 118140960795 + 2971082 * 2 ^ 59
def prefixEnd_2971082 : Nat := 4983230072969 + 3 ^ 40 * 2971082 * 2
def baseEnd_2971082 : Nat := 1525593129921649861711249

theorem tailTrace_2971082 : CollatzResearch.WordTrace tailWord_2971082 prefixEnd_2971082 1525593129921649861711249 := by
  unfold tailWord_2971082
  simp only [CollatzResearch.WordTrace]
  refine ⟨27091065755571202313226875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72242842014856539501938333 27091065755571202313226875)
  ·
    refine ⟨40636598633356803469840313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27091065755571202313226875 40636598633356803469840313)
    ·
      refine ⟨30477448975017602602380235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40636598633356803469840313 30477448975017602602380235)
      ·
        refine ⟨45716173462526403903570353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30477448975017602602380235 45716173462526403903570353)
        ·
          refine ⟨34287130096894802927677765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45716173462526403903570353 34287130096894802927677765)
          ·
            refine ⟨6428836893167775548939581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34287130096894802927677765 6428836893167775548939581)
            ·
              refine ⟨2410813834937915830852343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6428836893167775548939581 2410813834937915830852343)
              ·
                refine ⟨3616220752406873746278515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2410813834937915830852343 3616220752406873746278515)
                ·
                  refine ⟨5424331128610310619417773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616220752406873746278515 5424331128610310619417773)
                  ·
                    refine ⟨2034124173228866482281665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5424331128610310619417773 2034124173228866482281665)
                    ·
                      refine ⟨1525593129921649861711249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034124173228866482281665 1525593129921649861711249)
                      ·
                        rfl

theorem cell23_2971082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 4, 3, 1, 1, 3, 2].length) (baseStart_2971082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971082 prefixEnd_2971082 := by exact prefixLift 2971082
  have htrace : WordTrace (prefixWord ++ tailWord_2971082) baseStart_2971082 baseEnd_2971082 := by
    simpa [prefixWord, tailWord_2971082, baseEnd_2971082] using wordTrace_append hprefix tailTrace_2971082
  have hstable : (prefixWord ++ tailWord_2971082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971082).length < 2 ^ (prefixWord ++ tailWord_2971082).sum := by decide
  have hdescent : baseEnd_2971082 < baseStart_2971082 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971168 : List Nat := [2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2971168 : Nat := 118140960795 + 2971168 * 2 ^ 59
def prefixEnd_2971168 : Nat := 4983230072969 + 3 ^ 40 * 2971168 * 2
def baseEnd_2971168 : Nat := 1525637289257936525235853

theorem tailTrace_2971168 : CollatzResearch.WordTrace tailWord_2971168 prefixEnd_2971168 1525637289257936525235853 := by
  unfold tailWord_2971168
  simp only [CollatzResearch.WordTrace]
  refine ⟨54183699849986622970269079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72244933133315497293692105 54183699849986622970269079)
  ·
    refine ⟨81275549774979934455403619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54183699849986622970269079 81275549774979934455403619)
    ·
      refine ⟨121913324662469901683105429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81275549774979934455403619 121913324662469901683105429)
      ·
        refine ⟨5714687093553276641395567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 121913324662469901683105429 5714687093553276641395567)
        ·
          refine ⟨8572030640329914962093351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5714687093553276641395567 8572030640329914962093351)
          ·
            refine ⟨12858045960494872443140027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572030640329914962093351 12858045960494872443140027)
            ·
              refine ⟨19287068940742308664710041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12858045960494872443140027 19287068940742308664710041)
              ·
                refine ⟨14465301705556731498532531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19287068940742308664710041 14465301705556731498532531)
                ·
                  refine ⟨21697952558335097247798797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14465301705556731498532531 21697952558335097247798797)
                  ·
                    refine ⟨8136732209375661467924549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21697952558335097247798797 8136732209375661467924549)
                    ·
                      refine ⟨1525637289257936525235853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8136732209375661467924549 1525637289257936525235853)
                      ·
                        rfl

theorem cell23_2971168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2971168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971168 prefixEnd_2971168 := by exact prefixLift 2971168
  have htrace : WordTrace (prefixWord ++ tailWord_2971168) baseStart_2971168 baseEnd_2971168 := by
    simpa [prefixWord, tailWord_2971168, baseEnd_2971168] using wordTrace_append hprefix tailTrace_2971168
  have hstable : (prefixWord ++ tailWord_2971168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971168).length < 2 ^ (prefixWord ++ tailWord_2971168).sum := by decide
  have hdescent : baseEnd_2971168 < baseStart_2971168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971191 : List Nat := [1, 1, 3, 1, 2, 4, 1, 2, 8]
def baseStart_2971191 : Nat := 118140960795 + 2971191 * 2 ^ 59
def prefixEnd_2971191 : Nat := 4983230072969 + 3 ^ 40 * 2971191 * 2
def baseEnd_2971191 : Nat := 169516566590332215027583

theorem tailTrace_2971191 : CollatzResearch.WordTrace tailWord_2971191 prefixEnd_2971191 169516566590332215027583 := by
  unfold tailWord_2971191
  simp only [CollatzResearch.WordTrace]
  refine ⟨108368238578889920868625427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72245492385926613912416951 108368238578889920868625427)
  ·
    refine ⟨162552357868334881302938141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108368238578889920868625427 162552357868334881302938141)
    ·
      refine ⟨60957134200625580488601803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162552357868334881302938141 60957134200625580488601803)
      ·
        refine ⟨91435701300938370732902705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60957134200625580488601803 91435701300938370732902705)
        ·
          refine ⟨68576775975703778049677029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91435701300938370732902705 68576775975703778049677029)
          ·
            refine ⟨12858145495444458384314443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68576775975703778049677029 12858145495444458384314443)
            ·
              refine ⟨19287218243166687576471665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12858145495444458384314443 19287218243166687576471665)
              ·
                refine ⟨14465413682375015682353749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19287218243166687576471665 14465413682375015682353749)
                ·
                  refine ⟨169516566590332215027583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14465413682375015682353749 169516566590332215027583)
                  ·
                    rfl

theorem cell23_2971191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 2, 8].length) (baseStart_2971191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971191 prefixEnd_2971191 := by exact prefixLift 2971191
  have htrace : WordTrace (prefixWord ++ tailWord_2971191) baseStart_2971191 baseEnd_2971191 := by
    simpa [prefixWord, tailWord_2971191, baseEnd_2971191] using wordTrace_append hprefix tailTrace_2971191
  have hstable : (prefixWord ++ tailWord_2971191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971191).length < 2 ^ (prefixWord ++ tailWord_2971191).sum := by decide
  have hdescent : baseEnd_2971191 < baseStart_2971191 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971221 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 2, 9]
def baseStart_2971221 : Nat := 118140960795 + 2971221 * 2 ^ 59
def prefixEnd_2971221 : Nat := 4983230072969 + 3 ^ 40 * 2971221 * 2
def baseEnd_2971221 : Nat := 508554834577541605957703

theorem tailTrace_2971221 : CollatzResearch.WordTrace tailWord_2971221 prefixEnd_2971221 508554834577541605957703 := by
  unfold tailWord_2971221
  simp only [CollatzResearch.WordTrace]
  refine ⟨108369332768781235992217517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72246221845854157328145011 108369332768781235992217517)
  ·
    refine ⟨40638499788292963497081569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108369332768781235992217517 40638499788292963497081569)
    ·
      refine ⟨30478874841219722622811177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40638499788292963497081569 30478874841219722622811177)
      ·
        refine ⟨22859156130914791967108383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30478874841219722622811177 22859156130914791967108383)
        ·
          refine ⟨34288734196372187950662575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22859156130914791967108383 34288734196372187950662575)
          ·
            refine ⟨51433101294558281925993863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34288734196372187950662575 51433101294558281925993863)
            ·
              refine ⟨77149651941837422888990795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51433101294558281925993863 77149651941837422888990795)
              ·
                refine ⟨115724477912756134333486193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77149651941837422888990795 115724477912756134333486193)
                ·
                  refine ⟨86793358434567100750114645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115724477912756134333486193 86793358434567100750114645)
                  ·
                    refine ⟨508554834577541605957703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86793358434567100750114645 508554834577541605957703)
                    ·
                      rfl

theorem cell23_2971221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 9].length) (baseStart_2971221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971221 prefixEnd_2971221 := by exact prefixLift 2971221
  have htrace : WordTrace (prefixWord ++ tailWord_2971221) baseStart_2971221 baseEnd_2971221 := by
    simpa [prefixWord, tailWord_2971221, baseEnd_2971221] using wordTrace_append hprefix tailTrace_2971221
  have hstable : (prefixWord ++ tailWord_2971221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971221).length < 2 ^ (prefixWord ++ tailWord_2971221).sum := by decide
  have hdescent : baseEnd_2971221 < baseStart_2971221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971281 : List Nat := [1, 2, 2, 1, 1, 1, 1, 14]
def baseStart_2971281 : Nat := 118140960795 + 2971281 * 2 ^ 59
def prefixEnd_2971281 : Nat := 4983230072969 + 3 ^ 40 * 2971281 * 2
def baseEnd_2971281 : Nat := 56507233798959058634179

theorem tailTrace_2971281 : CollatzResearch.WordTrace tailWord_2971281 prefixEnd_2971281 56507233798959058634179 := by
  unfold tailWord_2971281
  simp only [CollatzResearch.WordTrace]
  refine ⟨108371521148563866239401697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72247680765709244159601131 108371521148563866239401697)
  ·
    refine ⟨81278640861422899679551273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108371521148563866239401697 81278640861422899679551273)
    ·
      refine ⟨60958980646067174759663455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81278640861422899679551273 60958980646067174759663455)
      ·
        refine ⟨91438470969100762139495183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60958980646067174759663455 91438470969100762139495183)
        ·
          refine ⟨137157706453651143209242775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91438470969100762139495183 137157706453651143209242775)
          ·
            refine ⟨205736559680476714813864163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137157706453651143209242775 205736559680476714813864163)
            ·
              refine ⟨308604839520715072220796245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205736559680476714813864163 308604839520715072220796245)
              ·
                refine ⟨56507233798959058634179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 14 308604839520715072220796245 56507233798959058634179)
                ·
                  rfl

theorem cell23_2971281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 14].length) (baseStart_2971281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971281 prefixEnd_2971281 := by exact prefixLift 2971281
  have htrace : WordTrace (prefixWord ++ tailWord_2971281) baseStart_2971281 baseEnd_2971281 := by
    simpa [prefixWord, tailWord_2971281, baseEnd_2971281] using wordTrace_append hprefix tailTrace_2971281
  have hstable : (prefixWord ++ tailWord_2971281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971281).length < 2 ^ (prefixWord ++ tailWord_2971281).sum := by decide
  have hdescent : baseEnd_2971281 < baseStart_2971281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971312 : List Nat := [2, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3]
def baseStart_2971312 : Nat := 118140960795 + 2971312 * 2 ^ 59
def prefixEnd_2971312 : Nat := 4983230072969 + 3 ^ 40 * 2971312 * 2
def baseEnd_2971312 : Nat := 1525711230472183961835191

theorem tailTrace_2971312 : CollatzResearch.WordTrace tailWord_2971312 prefixEnd_2971312 1525711230472183961835191 := by
  unfold tailWord_2971312
  simp only [CollatzResearch.WordTrace]
  refine ⟨54186325905725779266890095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72248434540967705689186793 54186325905725779266890095)
  ·
    refine ⟨81279488858588668900335143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54186325905725779266890095 81279488858588668900335143)
    ·
      refine ⟨121919233287883003350502715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81279488858588668900335143 121919233287883003350502715)
      ·
        refine ⟨182878849931824505025754073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121919233287883003350502715 182878849931824505025754073)
        ·
          refine ⟨137159137448868378769315555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182878849931824505025754073 137159137448868378769315555)
          ·
            refine ⟨205738706173302568153973333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137159137448868378769315555 205738706173302568153973333)
            ·
              refine ⟨2411000462968389470554375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 205738706173302568153973333 2411000462968389470554375)
              ·
                refine ⟨3616500694452584205831563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411000462968389470554375 3616500694452584205831563)
                ·
                  refine ⟨5424751041678876308747345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616500694452584205831563 5424751041678876308747345)
                  ·
                    refine ⟨4068563281259157231560509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5424751041678876308747345 4068563281259157231560509)
                    ·
                      refine ⟨1525711230472183961835191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4068563281259157231560509 1525711230472183961835191)
                      ·
                        rfl

theorem cell23_2971312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 8, 1, 1, 2, 3].length) (baseStart_2971312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971312 prefixEnd_2971312 := by exact prefixLift 2971312
  have htrace : WordTrace (prefixWord ++ tailWord_2971312) baseStart_2971312 baseEnd_2971312 := by
    simpa [prefixWord, tailWord_2971312, baseEnd_2971312] using wordTrace_append hprefix tailTrace_2971312
  have hstable : (prefixWord ++ tailWord_2971312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971312).length < 2 ^ (prefixWord ++ tailWord_2971312).sum := by decide
  have hdescent : baseEnd_2971312 < baseStart_2971312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971326 : List Nat := [4, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2]
def baseStart_2971326 : Nat := 118140960795 + 2971326 * 2 ^ 59
def prefixEnd_2971326 : Nat := 4983230072969 + 3 ^ 40 * 2971326 * 2
def baseEnd_2971326 : Nat := 1525718419201346907060127

theorem tailTrace_2971326 : CollatzResearch.WordTrace tailWord_2971326 prefixEnd_2971326 1525718419201346907060127 := by
  unfold tailWord_2971326
  simp only [CollatzResearch.WordTrace]
  refine ⟨13546645304175104865598729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72248774955600559283193221 13546645304175104865598729)
  ·
    refine ⟨10159983978131328649199047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13546645304175104865598729 10159983978131328649199047)
    ·
      refine ⟨15239975967196992973798571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10159983978131328649199047 15239975967196992973798571)
      ·
        refine ⟨22859963950795489460697857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15239975967196992973798571 22859963950795489460697857)
        ·
          refine ⟨17144972963096617095523393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22859963950795489460697857 17144972963096617095523393)
          ·
            refine ⟨12858729722322462821642545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17144972963096617095523393 12858729722322462821642545)
            ·
              refine ⟨9644047291741847116231909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12858729722322462821642545 9644047291741847116231909)
              ·
                refine ⟨1808258867201596334293483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9644047291741847116231909 1808258867201596334293483)
                ·
                  refine ⟨2712388300802394501440225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808258867201596334293483 2712388300802394501440225)
                  ·
                    refine ⟨2034291225601795876080169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712388300802394501440225 2034291225601795876080169)
                    ·
                      refine ⟨1525718419201346907060127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034291225601795876080169 1525718419201346907060127)
                      ·
                        rfl

theorem cell23_2971326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 2, 4, 1, 2, 2].length) (baseStart_2971326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971326 prefixEnd_2971326 := by exact prefixLift 2971326
  have htrace : WordTrace (prefixWord ++ tailWord_2971326) baseStart_2971326 baseEnd_2971326 := by
    simpa [prefixWord, tailWord_2971326, baseEnd_2971326] using wordTrace_append hprefix tailTrace_2971326
  have hstable : (prefixWord ++ tailWord_2971326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971326).length < 2 ^ (prefixWord ++ tailWord_2971326).sum := by decide
  have hdescent : baseEnd_2971326 < baseStart_2971326 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971442 : List Nat := [3, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2]
def baseStart_2971442 : Nat := 118140960795 + 2971442 * 2 ^ 59
def prefixEnd_2971442 : Nat := 4983230072969 + 3 ^ 40 * 2971442 * 2
def baseEnd_2971442 : Nat := 1525777982957268453209593

theorem tailTrace_2971442 : CollatzResearch.WordTrace tailWord_2971442 prefixEnd_2971442 1525777982957268453209593 := by
  unfold tailWord_2971442
  simp only [CollatzResearch.WordTrace]
  refine ⟨27094348325245147684003145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72251595533987060490675053 27094348325245147684003145)
  ·
    refine ⟨20320761243933860763002359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27094348325245147684003145 20320761243933860763002359)
    ·
      refine ⟨30481141865900791144503539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20320761243933860763002359 30481141865900791144503539)
      ·
        refine ⟨45721712798851186716755309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30481141865900791144503539 45721712798851186716755309)
        ·
          refine ⟨17145642299569195018783241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45721712798851186716755309 17145642299569195018783241)
          ·
            refine ⟨12859231724676896264087431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17145642299569195018783241 12859231724676896264087431)
            ·
              refine ⟨19288847587015344396131147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859231724676896264087431 19288847587015344396131147)
              ·
                refine ⟨28933271380523016594196721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19288847587015344396131147 28933271380523016594196721)
                ·
                  refine ⟨21699953535392262445647541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28933271380523016594196721 21699953535392262445647541)
                  ·
                    refine ⟨2034370643943024604279457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21699953535392262445647541 2034370643943024604279457)
                    ·
                      refine ⟨1525777982957268453209593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034370643943024604279457 1525777982957268453209593)
                      ·
                        rfl

theorem cell23_2971442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 2, 5, 2].length) (baseStart_2971442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971442 prefixEnd_2971442 := by exact prefixLift 2971442
  have htrace : WordTrace (prefixWord ++ tailWord_2971442) baseStart_2971442 baseEnd_2971442 := by
    simpa [prefixWord, tailWord_2971442, baseEnd_2971442] using wordTrace_append hprefix tailTrace_2971442
  have hstable : (prefixWord ++ tailWord_2971442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971442).length < 2 ^ (prefixWord ++ tailWord_2971442).sum := by decide
  have hdescent : baseEnd_2971442 < baseStart_2971442 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971449 : List Nat := [1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2971449 : Nat := 118140960795 + 2971449 * 2 ^ 59
def prefixEnd_2971449 : Nat := 4983230072969 + 3 ^ 40 * 2971449 * 2
def baseEnd_2971449 : Nat := 1525781577321849925822061

theorem tailTrace_2971449 : CollatzResearch.WordTrace tailWord_2971449 prefixEnd_2971449 1525781577321849925822061 := by
  unfold tailWord_2971449
  simp only [CollatzResearch.WordTrace]
  refine ⟨108377648611955230931517401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72251765741303487287678267 108377648611955230931517401)
  ·
    refine ⟨81283236458966423198638051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108377648611955230931517401 81283236458966423198638051)
    ·
      refine ⟨121924854688449634797957077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81283236458966423198638051 121924854688449634797957077)
      ·
        refine ⟨2857613781760538315577119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 121924854688449634797957077 2857613781760538315577119)
        ·
          refine ⟨4286420672640807473365679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2857613781760538315577119 4286420672640807473365679)
          ·
            refine ⟨6429631008961211210048519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4286420672640807473365679 6429631008961211210048519)
            ·
              refine ⟨9644446513441816815072779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6429631008961211210048519 9644446513441816815072779)
              ·
                refine ⟨14466669770162725222609169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9644446513441816815072779 14466669770162725222609169)
                ·
                  refine ⟨10850002327622043916956877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14466669770162725222609169 10850002327622043916956877)
                  ·
                    refine ⟨4068750872858266468858829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10850002327622043916956877 4068750872858266468858829)
                    ·
                      refine ⟨1525781577321849925822061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4068750872858266468858829 1525781577321849925822061)
                      ·
                        rfl

theorem cell23_2971449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2971449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971449 prefixEnd_2971449 := by exact prefixLift 2971449
  have htrace : WordTrace (prefixWord ++ tailWord_2971449) baseStart_2971449 baseEnd_2971449 := by
    simpa [prefixWord, tailWord_2971449, baseEnd_2971449] using wordTrace_append hprefix tailTrace_2971449
  have hstable : (prefixWord ++ tailWord_2971449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971449).length < 2 ^ (prefixWord ++ tailWord_2971449).sum := by decide
  have hdescent : baseEnd_2971449 < baseStart_2971449 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971469 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 2, 5]
def baseStart_2971469 : Nat := 118140960795 + 2971469 * 2 ^ 59
def prefixEnd_2971469 : Nat := 4983230072969 + 3 ^ 40 * 2971469 * 2
def baseEnd_2971469 : Nat := 508597282311646615857323

theorem tailTrace_2971469 : CollatzResearch.WordTrace tailWord_2971469 prefixEnd_2971469 508597282311646615857323 := by
  unfold tailWord_2971469
  simp only [CollatzResearch.WordTrace]
  refine ⟨108378378071882774347245461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72252252047921849564830307 108378378071882774347245461)
  ·
    refine ⟨5080236472119505047527131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108378378071882774347245461 5080236472119505047527131)
    ·
      refine ⟨7620354708179257571290697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5080236472119505047527131 7620354708179257571290697)
      ·
        refine ⟨5715266031134443178468023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7620354708179257571290697 5715266031134443178468023)
        ·
          refine ⟨8572899046701664767702035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715266031134443178468023 8572899046701664767702035)
          ·
            refine ⟨12859348570052497151553053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8572899046701664767702035 12859348570052497151553053)
            ·
              refine ⟨4822255713769686431832395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12859348570052497151553053 4822255713769686431832395)
              ·
                refine ⟨7233383570654529647748593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822255713769686431832395 7233383570654529647748593)
                ·
                  refine ⟨5425037677990897235811445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7233383570654529647748593 5425037677990897235811445)
                  ·
                    refine ⟨508597282311646615857323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5425037677990897235811445 508597282311646615857323)
                    ·
                      rfl

theorem cell23_2971469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 2, 5].length) (baseStart_2971469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971469 prefixEnd_2971469 := by exact prefixLift 2971469
  have htrace : WordTrace (prefixWord ++ tailWord_2971469) baseStart_2971469 baseEnd_2971469 := by
    simpa [prefixWord, tailWord_2971469, baseEnd_2971469] using wordTrace_append hprefix tailTrace_2971469
  have hstable : (prefixWord ++ tailWord_2971469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971469).length < 2 ^ (prefixWord ++ tailWord_2971469).sum := by decide
  have hdescent : baseEnd_2971469 < baseStart_2971469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971495 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 8]
def baseStart_2971495 : Nat := 118140960795 + 2971495 * 2 ^ 59
def prefixEnd_2971495 : Nat := 4983230072969 + 3 ^ 40 * 2971495 * 2
def baseEnd_2971495 : Nat := 169533910825772971760761

theorem tailTrace_2971495 : CollatzResearch.WordTrace tailWord_2971495 prefixEnd_2971495 169533910825772971760761 := by
  unfold tailWord_2971495
  simp only [CollatzResearch.WordTrace]
  refine ⟨108379326369788580787691939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72252884246525720525127959 108379326369788580787691939)
  ·
    refine ⟨162568989554682871181537909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108379326369788580787691939 162568989554682871181537909)
    ·
      refine ⟨15240842770751519173269179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162568989554682871181537909 15240842770751519173269179)
      ·
        refine ⟨22861264156127278759903769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15240842770751519173269179 22861264156127278759903769)
        ·
          refine ⟨17145948117095459069927827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22861264156127278759903769 17145948117095459069927827)
          ·
            refine ⟨25718922175643188604891741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17145948117095459069927827 25718922175643188604891741)
            ·
              refine ⟨9644595815866195726834403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25718922175643188604891741 9644595815866195726834403)
              ·
                refine ⟨14466893723799293590251605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9644595815866195726834403 14466893723799293590251605)
                ·
                  refine ⟨169533910825772971760761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14466893723799293590251605 169533910825772971760761)
                  ·
                    rfl

theorem cell23_2971495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 8].length) (baseStart_2971495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971495 prefixEnd_2971495 := by exact prefixLift 2971495
  have htrace : WordTrace (prefixWord ++ tailWord_2971495) baseStart_2971495 baseEnd_2971495 := by
    simpa [prefixWord, tailWord_2971495, baseEnd_2971495] using wordTrace_append hprefix tailTrace_2971495
  have hstable : (prefixWord ++ tailWord_2971495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971495).length < 2 ^ (prefixWord ++ tailWord_2971495).sum := by decide
  have hdescent : baseEnd_2971495 < baseStart_2971495 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971549 : List Nat := [1, 4, 2, 1, 2, 2, 1, 1, 4, 3, 2]
def baseStart_2971549 : Nat := 118140960795 + 2971549 * 2 ^ 59
def prefixEnd_2971549 : Nat := 4983230072969 + 3 ^ 40 * 2971549 * 2
def baseEnd_2971549 : Nat := 1525832925387299534571601

theorem tailTrace_2971549 : CollatzResearch.WordTrace tailWord_2971549 prefixEnd_2971549 1525832925387299534571601 := by
  unfold tailWord_2971549
  simp only [CollatzResearch.WordTrace]
  refine ⟨108381295911592948010157701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72254197274395298673438467 108381295911592948010157701)
  ·
    refine ⟨20321492983423677751904569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108381295911592948010157701 20321492983423677751904569)
    ·
      refine ⟨15241119737567758313928427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20321492983423677751904569 15241119737567758313928427)
      ·
        refine ⟨22861679606351637470892641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15241119737567758313928427 22861679606351637470892641)
        ·
          refine ⟨17146259704763728103169481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22861679606351637470892641 17146259704763728103169481)
          ·
            refine ⟨12859694778572796077377111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17146259704763728103169481 12859694778572796077377111)
            ·
              refine ⟨19289542167859194116065667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859694778572796077377111 19289542167859194116065667)
              ·
                refine ⟨28934313251788791174098501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19289542167859194116065667 28934313251788791174098501)
                ·
                  refine ⟨5425183734710398345143469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28934313251788791174098501 5425183734710398345143469)
                  ·
                    refine ⟨2034443900516399379428801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5425183734710398345143469 2034443900516399379428801)
                    ·
                      refine ⟨1525832925387299534571601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034443900516399379428801 1525832925387299534571601)
                      ·
                        rfl

theorem cell23_2971549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 3, 2].length) (baseStart_2971549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971549 prefixEnd_2971549 := by exact prefixLift 2971549
  have htrace : WordTrace (prefixWord ++ tailWord_2971549) baseStart_2971549 baseEnd_2971549 := by
    simpa [prefixWord, tailWord_2971549, baseEnd_2971549] using wordTrace_append hprefix tailTrace_2971549
  have hstable : (prefixWord ++ tailWord_2971549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971549).length < 2 ^ (prefixWord ++ tailWord_2971549).sum := by decide
  have hdescent : baseEnd_2971549 < baseStart_2971549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971550 : List Nat := [4, 3, 1, 3, 2, 1, 1, 1, 3, 4]
def baseStart_2971550 : Nat := 118140960795 + 2971550 * 2 ^ 59
def prefixEnd_2971550 : Nat := 4983230072969 + 3 ^ 40 * 2971550 * 2
def baseEnd_2971550 : Nat := 508611146289318010219699

theorem tailTrace_2971550 : CollatzResearch.WordTrace tailWord_2971550 prefixEnd_2971550 508611146289318010219699 := by
  unfold tailWord_2971550
  simp only [CollatzResearch.WordTrace]
  refine ⟨13547666548073665647618013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72254221589726216787296069 13547666548073665647618013)
  ·
    refine ⟨5080374955527624617856755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13547666548073665647618013 5080374955527624617856755)
    ·
      refine ⟨7620562433291436926785133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5080374955527624617856755 7620562433291436926785133)
      ·
        refine ⟨2857710912484288847544425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7620562433291436926785133 2857710912484288847544425)
        ·
          refine ⟨2143283184363216635658319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2857710912484288847544425 2143283184363216635658319)
          ·
            refine ⟨3214924776544824953487479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143283184363216635658319 3214924776544824953487479)
            ·
              refine ⟨4822387164817237430231219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214924776544824953487479 4822387164817237430231219)
              ·
                refine ⟨7233580747225856145346829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822387164817237430231219 7233580747225856145346829)
                ·
                  refine ⟨2712592780209696054505061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7233580747225856145346829 2712592780209696054505061)
                  ·
                    refine ⟨508611146289318010219699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2712592780209696054505061 508611146289318010219699)
                    ·
                      rfl

theorem cell23_2971550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 3, 4].length) (baseStart_2971550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971550 prefixEnd_2971550 := by exact prefixLift 2971550
  have htrace : WordTrace (prefixWord ++ tailWord_2971550) baseStart_2971550 baseEnd_2971550 := by
    simpa [prefixWord, tailWord_2971550, baseEnd_2971550] using wordTrace_append hprefix tailTrace_2971550
  have hstable : (prefixWord ++ tailWord_2971550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971550).length < 2 ^ (prefixWord ++ tailWord_2971550).sum := by decide
  have hdescent : baseEnd_2971550 < baseStart_2971550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971556 : List Nat := [2, 3, 1, 2, 1, 5, 1, 1, 3, 1, 3]
def baseStart_2971556 : Nat := 118140960795 + 2971556 * 2 ^ 59
def prefixEnd_2971556 : Nat := 4983230072969 + 3 ^ 40 * 2971556 * 2
def baseEnd_2971556 : Nat := 1525836519751881007184069

theorem tailTrace_2971556 : CollatzResearch.WordTrace tailWord_2971556 prefixEnd_2971556 1525836519751881007184069 := by
  unfold tailWord_2971556
  simp only [CollatzResearch.WordTrace]
  refine ⟨54190775611283794102831261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72254367481711725470441681 54190775611283794102831261)
  ·
    refine ⟨20321540854231422788561723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54190775611283794102831261 20321540854231422788561723)
    ·
      refine ⟨30482311281347134182842585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20321540854231422788561723 30482311281347134182842585)
      ·
        refine ⟨22861733461010350637131939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30482311281347134182842585 22861733461010350637131939)
        ·
          refine ⟨34292600191515525955697909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22861733461010350637131939 34292600191515525955697909)
          ·
            refine ⟨3214931267954580558346679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34292600191515525955697909 3214931267954580558346679)
            ·
              refine ⟨4822396901931870837520019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3214931267954580558346679 4822396901931870837520019)
              ·
                refine ⟨7233595352897806256280029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822396901931870837520019 7233595352897806256280029)
                ·
                  refine ⟨2712598257336677346105011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7233595352897806256280029 2712598257336677346105011)
                  ·
                    refine ⟨4068897386005016019157517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2712598257336677346105011 4068897386005016019157517)
                    ·
                      refine ⟨1525836519751881007184069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4068897386005016019157517 1525836519751881007184069)
                      ·
                        rfl

theorem cell23_2971556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 5, 1, 1, 3, 1, 3].length) (baseStart_2971556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971556 prefixEnd_2971556 := by exact prefixLift 2971556
  have htrace : WordTrace (prefixWord ++ tailWord_2971556) baseStart_2971556 baseEnd_2971556 := by
    simpa [prefixWord, tailWord_2971556, baseEnd_2971556] using wordTrace_append hprefix tailTrace_2971556
  have hstable : (prefixWord ++ tailWord_2971556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971556).length < 2 ^ (prefixWord ++ tailWord_2971556).sum := by decide
  have hdescent : baseEnd_2971556 < baseStart_2971556 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971592 : List Nat := [2, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4]
def baseStart_2971592 : Nat := 118140960795 + 2971592 * 2 ^ 59
def prefixEnd_2971592 : Nat := 4983230072969 + 3 ^ 40 * 2971592 * 2
def baseEnd_2971592 : Nat := 1525855005055442866333903

theorem tailTrace_2971592 : CollatzResearch.WordTrace tailWord_2971592 prefixEnd_2971592 1525855005055442866333903 := by
  unfold tailWord_2971592
  simp only [CollatzResearch.WordTrace]
  refine ⟨54191432125218583176986515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72255242833624777569315353 54191432125218583176986515)
  ·
    refine ⟨81287148187827874765479773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54191432125218583176986515 81287148187827874765479773)
    ·
      refine ⟨30482680570435453037054915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81287148187827874765479773 30482680570435453037054915)
      ·
        refine ⟨45724020855653179555582373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30482680570435453037054915 45724020855653179555582373)
        ·
          refine ⟨8573253910434971166671695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45724020855653179555582373 8573253910434971166671695)
          ·
            refine ⟨12859880865652456750007543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573253910434971166671695 12859880865652456750007543)
            ·
              refine ⟨19289821298478685125011315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12859880865652456750007543 19289821298478685125011315)
              ·
                refine ⟨28934731947718027687516973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19289821298478685125011315 28934731947718027687516973)
                ·
                  refine ⟨10850524480394260382818865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28934731947718027687516973 10850524480394260382818865)
                  ·
                    refine ⟨8137893360295695287114149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10850524480394260382818865 8137893360295695287114149)
                    ·
                      refine ⟨1525855005055442866333903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8137893360295695287114149 1525855005055442866333903)
                      ·
                        rfl

theorem cell23_2971592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 3, 2, 4].length) (baseStart_2971592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971592 prefixEnd_2971592 := by exact prefixLift 2971592
  have htrace : WordTrace (prefixWord ++ tailWord_2971592) baseStart_2971592 baseEnd_2971592 := by
    simpa [prefixWord, tailWord_2971592, baseEnd_2971592] using wordTrace_append hprefix tailTrace_2971592
  have hstable : (prefixWord ++ tailWord_2971592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971592).length < 2 ^ (prefixWord ++ tailWord_2971592).sum := by decide
  have hdescent : baseEnd_2971592 < baseStart_2971592 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971596 : List Nat := [2, 2, 1, 4, 1, 3, 3, 1, 1, 1, 4]
def baseStart_2971596 : Nat := 118140960795 + 2971596 * 2 ^ 59
def prefixEnd_2971596 : Nat := 4983230072969 + 3 ^ 40 * 2971596 * 2
def baseEnd_2971596 : Nat := 1525857058978060850683885

theorem tailTrace_2971596 : CollatzResearch.WordTrace tailWord_2971596 prefixEnd_2971596 1525857058978060850683885 := by
  unfold tailWord_2971596
  simp only [CollatzResearch.WordTrace]
  refine ⟨54191505071211337518559321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72255340094948450024745761 54191505071211337518559321)
  ·
    refine ⟨40643628803408503138919491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54191505071211337518559321 40643628803408503138919491)
    ·
      refine ⟨60965443205112754708379237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40643628803408503138919491 60965443205112754708379237)
      ·
        refine ⟨11431020600958641507821107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60965443205112754708379237 11431020600958641507821107)
        ·
          refine ⟨17146530901437962261731661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11431020600958641507821107 17146530901437962261731661)
          ·
            refine ⟨6429949088039235848149373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17146530901437962261731661 6429949088039235848149373)
            ·
              refine ⟨2411230908014713443056015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6429949088039235848149373 2411230908014713443056015)
              ·
                refine ⟨3616846362022070164584023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411230908014713443056015 3616846362022070164584023)
                ·
                  refine ⟨5425269543033105246876035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616846362022070164584023 5425269543033105246876035)
                  ·
                    refine ⟨8137904314549657870314053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5425269543033105246876035 8137904314549657870314053)
                    ·
                      refine ⟨1525857058978060850683885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8137904314549657870314053 1525857058978060850683885)
                      ·
                        rfl

theorem cell23_2971596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 3, 1, 1, 1, 4].length) (baseStart_2971596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971596 prefixEnd_2971596 := by exact prefixLift 2971596
  have htrace : WordTrace (prefixWord ++ tailWord_2971596) baseStart_2971596 baseEnd_2971596 := by
    simpa [prefixWord, tailWord_2971596, baseEnd_2971596] using wordTrace_append hprefix tailTrace_2971596
  have hstable : (prefixWord ++ tailWord_2971596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971596).length < 2 ^ (prefixWord ++ tailWord_2971596).sum := by decide
  have hdescent : baseEnd_2971596 < baseStart_2971596 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971602 : List Nat := [3, 2, 2, 3, 2, 11]
def baseStart_2971602 : Nat := 118140960795 + 2971602 * 2 ^ 59
def prefixEnd_2971602 : Nat := 4983230072969 + 3 ^ 40 * 2971602 * 2
def baseEnd_2971602 : Nat := 6279259834822995173699

theorem tailTrace_2971602 : CollatzResearch.WordTrace tailWord_2971602 prefixEnd_2971602 6279259834822995173699 := by
  unfold tailWord_2971602
  simp only [CollatzResearch.WordTrace]
  refine ⟨27095807245100234515459265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72255485986933958707891373 27095807245100234515459265)
  ·
    refine ⟨20321855433825175886594449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27095807245100234515459265 20321855433825175886594449)
    ·
      refine ⟨15241391575368881914945837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20321855433825175886594449 15241391575368881914945837)
      ·
        refine ⟨5715521840763330718104689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15241391575368881914945837 5715521840763330718104689)
        ·
          refine ⟨4286641380572498038578517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5715521840763330718104689 4286641380572498038578517)
          ·
            refine ⟨6279259834822995173699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 4286641380572498038578517 6279259834822995173699)
            ·
              rfl

theorem cell23_2971602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 11].length) (baseStart_2971602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971602 prefixEnd_2971602 := by exact prefixLift 2971602
  have htrace : WordTrace (prefixWord ++ tailWord_2971602) baseStart_2971602 baseEnd_2971602 := by
    simpa [prefixWord, tailWord_2971602, baseEnd_2971602] using wordTrace_append hprefix tailTrace_2971602
  have hstable : (prefixWord ++ tailWord_2971602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971602).length < 2 ^ (prefixWord ++ tailWord_2971602).sum := by decide
  have hdescent : baseEnd_2971602 < baseStart_2971602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971646 : List Nat := [4, 2, 2, 2, 1, 1, 2, 2, 1, 3, 3]
def baseStart_2971646 : Nat := 118140960795 + 2971646 * 2 ^ 59
def prefixEnd_2971646 : Nat := 4983230072969 + 3 ^ 40 * 2971646 * 2
def baseEnd_2971646 : Nat := 1525882733010785655058655

theorem tailTrace_2971646 : CollatzResearch.WordTrace tailWord_2971646 prefixEnd_2971646 1525882733010785655058655 := by
  unfold tailWord_2971646
  simp only [CollatzResearch.WordTrace]
  refine ⟨13548104224030191697054849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72256555861494355717625861 13548104224030191697054849)
  ·
    refine ⟨10161078168022643772791137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13548104224030191697054849 10161078168022643772791137)
    ·
      refine ⟨7620808626016982829593353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10161078168022643772791137 7620808626016982829593353)
      ·
        refine ⟨5715606469512737122195015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7620808626016982829593353 5715606469512737122195015)
        ·
          refine ⟨8573409704269105683292523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5715606469512737122195015 8573409704269105683292523)
          ·
            refine ⟨12860114556403658524938785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8573409704269105683292523 12860114556403658524938785)
            ·
              refine ⟨9645085917302743893704089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12860114556403658524938785 9645085917302743893704089)
              ·
                refine ⟨7233814437977057920278067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9645085917302743893704089 7233814437977057920278067)
                ·
                  refine ⟨10850721656965586880417101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7233814437977057920278067 10850721656965586880417101)
                  ·
                    refine ⟨4069020621362095080156413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10850721656965586880417101 4069020621362095080156413)
                    ·
                      refine ⟨1525882733010785655058655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069020621362095080156413 1525882733010785655058655)
                      ·
                        rfl

theorem cell23_2971646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 2, 1, 3, 3].length) (baseStart_2971646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971646 prefixEnd_2971646 := by exact prefixLift 2971646
  have htrace : WordTrace (prefixWord ++ tailWord_2971646) baseStart_2971646 baseEnd_2971646 := by
    simpa [prefixWord, tailWord_2971646, baseEnd_2971646] using wordTrace_append hprefix tailTrace_2971646
  have hstable : (prefixWord ++ tailWord_2971646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971646).length < 2 ^ (prefixWord ++ tailWord_2971646).sum := by decide
  have hdescent : baseEnd_2971646 < baseStart_2971646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971656 : List Nat := [2, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2]
def baseStart_2971656 : Nat := 118140960795 + 2971656 * 2 ^ 59
def prefixEnd_2971656 : Nat := 4983230072969 + 3 ^ 40 * 2971656 * 2
def baseEnd_2971656 : Nat := 1525887867817330615933609

theorem tailTrace_2971656 : CollatzResearch.WordTrace tailWord_2971656 prefixEnd_2971656 1525887867817330615933609 := by
  unfold tailWord_2971656
  simp only [CollatzResearch.WordTrace]
  refine ⟨54192599261102652642151411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72256799014803536856201881 54192599261102652642151411)
  ·
    refine ⟨81288898891653978963227117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54192599261102652642151411 81288898891653978963227117)
    ·
      refine ⟨30483337084370242111210169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81288898891653978963227117 30483337084370242111210169)
      ·
        refine ⟨22862502813277681583407627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30483337084370242111210169 22862502813277681583407627)
        ·
          refine ⟨34293754219916522375111441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22862502813277681583407627 34293754219916522375111441)
          ·
            refine ⟨25720315664937391781333581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34293754219916522375111441 25720315664937391781333581)
            ·
              refine ⟨9645118374351521918000093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25720315664937391781333581 9645118374351521918000093)
              ·
                refine ⟨3616919390381820719250035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9645118374351521918000093 3616919390381820719250035)
                ·
                  refine ⟨5425379085572731078875053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3616919390381820719250035 5425379085572731078875053)
                  ·
                    refine ⟨2034517157089774154578145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5425379085572731078875053 2034517157089774154578145)
                    ·
                      refine ⟨1525887867817330615933609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034517157089774154578145 1525887867817330615933609)
                      ·
                        rfl

theorem cell23_2971656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 2, 3, 3, 1, 3, 2].length) (baseStart_2971656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971656 prefixEnd_2971656 := by exact prefixLift 2971656
  have htrace : WordTrace (prefixWord ++ tailWord_2971656) baseStart_2971656 baseEnd_2971656 := by
    simpa [prefixWord, tailWord_2971656, baseEnd_2971656] using wordTrace_append hprefix tailTrace_2971656
  have hstable : (prefixWord ++ tailWord_2971656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971656).length < 2 ^ (prefixWord ++ tailWord_2971656).sum := by decide
  have hdescent : baseEnd_2971656 < baseStart_2971656 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971662 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 4, 6]
def baseStart_2971662 : Nat := 118140960795 + 2971662 * 2 ^ 59
def prefixEnd_2971662 : Nat := 4983230072969 + 3 ^ 40 * 2971662 * 2
def baseEnd_2971662 : Nat := 508630316233752530819527

theorem tailTrace_2971662 : CollatzResearch.WordTrace tailWord_2971662 prefixEnd_2971662 508630316233752530819527 := by
  unfold tailWord_2971662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13548177170022946038627655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72256944906789045539347493 13548177170022946038627655)
  ·
    refine ⟨20322265755034419057941483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13548177170022946038627655 20322265755034419057941483)
    ·
      refine ⟨30483398632551628586912225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20322265755034419057941483 30483398632551628586912225)
      ·
        refine ⟨22862548974413721440184169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30483398632551628586912225 22862548974413721440184169)
        ·
          refine ⟨17146911730810291080138127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22862548974413721440184169 17146911730810291080138127)
          ·
            refine ⟨25720367596215436620207191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17146911730810291080138127 25720367596215436620207191)
            ·
              refine ⟨38580551394323154930310787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25720367596215436620207191 38580551394323154930310787)
              ·
                refine ⟨57870827091484732395466181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38580551394323154930310787 57870827091484732395466181)
                ·
                  refine ⟨10850780079653387324149909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57870827091484732395466181 10850780079653387324149909)
                  ·
                    refine ⟨508630316233752530819527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10850780079653387324149909 508630316233752530819527)
                    ·
                      rfl

theorem cell23_2971662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 4, 6].length) (baseStart_2971662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971662 prefixEnd_2971662 := by exact prefixLift 2971662
  have htrace : WordTrace (prefixWord ++ tailWord_2971662) baseStart_2971662 baseEnd_2971662 := by
    simpa [prefixWord, tailWord_2971662, baseEnd_2971662] using wordTrace_append hprefix tailTrace_2971662
  have hstable : (prefixWord ++ tailWord_2971662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971662).length < 2 ^ (prefixWord ++ tailWord_2971662).sum := by decide
  have hdescent : baseEnd_2971662 < baseStart_2971662 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971729 : List Nat := [1, 2, 2, 1, 3, 1, 1, 3, 2, 5, 2]
def baseStart_2971729 : Nat := 118140960795 + 2971729 * 2 ^ 59
def prefixEnd_2971729 : Nat := 4983230072969 + 3 ^ 40 * 2971729 * 2
def baseEnd_2971729 : Nat := 1525925351905108830320773

theorem tailTrace_2971729 : CollatzResearch.WordTrace tailWord_2971729 prefixEnd_2971729 1525925351905108830320773 := by
  unfold tailWord_2971729
  simp only [CollatzResearch.WordTrace]
  refine ⟨108387861050940838751710241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72258574033960559167806827 108387861050940838751710241)
  ·
    refine ⟨81290895788205629063782681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108387861050940838751710241 81290895788205629063782681)
    ·
      refine ⟨60968171841154221797837011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81290895788205629063782681 60968171841154221797837011)
      ·
        refine ⟨91452257761731332696755517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60968171841154221797837011 91452257761731332696755517)
        ·
          refine ⟨34294596660649249761283319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91452257761731332696755517 34294596660649249761283319)
          ·
            refine ⟨51441894990973874641924979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34294596660649249761283319 51441894990973874641924979)
            ·
              refine ⟨77162842486460811962887469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51441894990973874641924979 77162842486460811962887469)
              ·
                refine ⟨28936065932422804486082801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 77162842486460811962887469 28936065932422804486082801)
                ·
                  refine ⟨21702049449317103364562101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28936065932422804486082801 21702049449317103364562101)
                  ·
                    refine ⟨2034567135873478440427697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21702049449317103364562101 2034567135873478440427697)
                    ·
                      refine ⟨1525925351905108830320773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034567135873478440427697 1525925351905108830320773)
                      ·
                        rfl

theorem cell23_2971729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 5, 2].length) (baseStart_2971729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971729 prefixEnd_2971729 := by exact prefixLift 2971729
  have htrace : WordTrace (prefixWord ++ tailWord_2971729) baseStart_2971729 baseEnd_2971729 := by
    simpa [prefixWord, tailWord_2971729, baseEnd_2971729] using wordTrace_append hprefix tailTrace_2971729
  have hstable : (prefixWord ++ tailWord_2971729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971729).length < 2 ^ (prefixWord ++ tailWord_2971729).sum := by decide
  have hdescent : baseEnd_2971729 < baseStart_2971729 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971759 : List Nat := [1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4]
def baseStart_2971759 : Nat := 118140960795 + 2971759 * 2 ^ 59
def prefixEnd_2971759 : Nat := 4983230072969 + 3 ^ 40 * 2971759 * 2
def baseEnd_2971759 : Nat := 1525940756324743712945635

theorem tailTrace_2971759 : CollatzResearch.WordTrace tailWord_2971759 prefixEnd_2971759 1525940756324743712945635 := by
  unfold tailWord_2971759
  simp only [CollatzResearch.WordTrace]
  refine ⟨108388955240832153875302331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72259303493888102583534887 108388955240832153875302331)
  ·
    refine ⟨162583432861248230812953497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108388955240832153875302331 162583432861248230812953497)
    ·
      refine ⟨121937574645936173109715123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162583432861248230812953497 121937574645936173109715123)
      ·
        refine ⟨182906361968904259664572685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121937574645936173109715123 182906361968904259664572685)
        ·
          refine ⟨68589885738339097374214757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182906361968904259664572685 68589885738339097374214757)
          ·
            refine ⟨12860603575938580757665267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68589885738339097374214757 12860603575938580757665267)
            ·
              refine ⟨19290905363907871136497901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12860603575938580757665267 19290905363907871136497901)
              ·
                refine ⟨7234089511465451676186713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19290905363907871136497901 7234089511465451676186713)
                ·
                  refine ⟨5425567133599088757140035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7234089511465451676186713 5425567133599088757140035)
                  ·
                    refine ⟨8138350700398633135710053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5425567133599088757140035 8138350700398633135710053)
                    ·
                      refine ⟨1525940756324743712945635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8138350700398633135710053 1525940756324743712945635)
                      ·
                        rfl

theorem cell23_2971759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 3, 2, 1, 4].length) (baseStart_2971759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971759 prefixEnd_2971759 := by exact prefixLift 2971759
  have htrace : WordTrace (prefixWord ++ tailWord_2971759) baseStart_2971759 baseEnd_2971759 := by
    simpa [prefixWord, tailWord_2971759, baseEnd_2971759] using wordTrace_append hprefix tailTrace_2971759
  have hstable : (prefixWord ++ tailWord_2971759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971759).length < 2 ^ (prefixWord ++ tailWord_2971759).sum := by decide
  have hdescent : baseEnd_2971759 < baseStart_2971759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971826 : List Nat := [3, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3]
def baseStart_2971826 : Nat := 118140960795 + 2971826 * 2 ^ 59
def prefixEnd_2971826 : Nat := 4983230072969 + 3 ^ 40 * 2971826 * 2
def baseEnd_2971826 : Nat := 1525975159528594950807827

theorem tailTrace_2971826 : CollatzResearch.WordTrace tailWord_2971826 prefixEnd_2971826 1525975159528594950807827 := by
  unfold tailWord_2971826
  simp only [CollatzResearch.WordTrace]
  refine ⟨27097849732897356079497833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72260932621059616211994221 27097849732897356079497833)
  ·
    refine ⟨20323387299673017059623375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27097849732897356079497833 20323387299673017059623375)
    ·
      refine ⟨30485080949509525589435063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20323387299673017059623375 30485080949509525589435063)
      ·
        refine ⟨45727621424264288384152595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30485080949509525589435063 45727621424264288384152595)
        ·
          refine ⟨68591432136396432576228893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45727621424264288384152595 68591432136396432576228893)
          ·
            refine ⟨25721787051148662216085835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68591432136396432576228893 25721787051148662216085835)
            ·
              refine ⟨38582680576722993324128753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25721787051148662216085835 38582680576722993324128753)
              ·
                refine ⟨28937010432542244993096565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38582680576722993324128753 28937010432542244993096565)
                ·
                  refine ⟨2712844728050835468102803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28937010432542244993096565 2712844728050835468102803)
                  ·
                    refine ⟨4069267092076253202154205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2712844728050835468102803 4069267092076253202154205)
                    ·
                      refine ⟨1525975159528594950807827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069267092076253202154205 1525975159528594950807827)
                      ·
                        rfl

theorem cell23_2971826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 2, 5, 1, 3].length) (baseStart_2971826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971826 prefixEnd_2971826 := by exact prefixLift 2971826
  have htrace : WordTrace (prefixWord ++ tailWord_2971826) baseStart_2971826 baseEnd_2971826 := by
    simpa [prefixWord, tailWord_2971826, baseEnd_2971826] using wordTrace_append hprefix tailTrace_2971826
  have hstable : (prefixWord ++ tailWord_2971826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971826).length < 2 ^ (prefixWord ++ tailWord_2971826).sum := by decide
  have hdescent : baseEnd_2971826 < baseStart_2971826 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971849 : List Nat := [1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 4]
def baseStart_2971849 : Nat := 118140960795 + 2971849 * 2 ^ 59
def prefixEnd_2971849 : Nat := 4983230072969 + 3 ^ 40 * 2971849 * 2
def baseEnd_2971849 : Nat := 1525986969583648360820221

theorem tailTrace_2971849 : CollatzResearch.WordTrace tailWord_2971849 prefixEnd_2971849 1525986969583648360820221 := by
  unfold tailWord_2971849
  simp only [CollatzResearch.WordTrace]
  refine ⟨108392237810506099246078601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72261491873670732830719067 108392237810506099246078601)
  ·
    refine ⟨81294178357879574434558951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108392237810506099246078601 81294178357879574434558951)
    ·
      refine ⟨121941267536819361651838427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81294178357879574434558951 121941267536819361651838427)
      ·
        refine ⟨182911901305229042477757641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121941267536819361651838427 182911901305229042477757641)
        ·
          refine ⟨137183925978921781858318231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 182911901305229042477757641 137183925978921781858318231)
          ·
            refine ⟨205775888968382672787477347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137183925978921781858318231 205775888968382672787477347)
            ·
              refine ⟨308663833452574009181216021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205775888968382672787477347 308663833452574009181216021)
              ·
                refine ⟨14468617193089406680369501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 308663833452574009181216021 14468617193089406680369501)
                ·
                  refine ⟨5425731447408527505138563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14468617193089406680369501 5425731447408527505138563)
                  ·
                    refine ⟨8138597171112791257707845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5425731447408527505138563 8138597171112791257707845)
                    ·
                      refine ⟨1525986969583648360820221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8138597171112791257707845 1525986969583648360820221)
                      ·
                        rfl

theorem cell23_2971849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 6, 3, 1, 4].length) (baseStart_2971849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971849 prefixEnd_2971849 := by exact prefixLift 2971849
  have htrace : WordTrace (prefixWord ++ tailWord_2971849) baseStart_2971849 baseEnd_2971849 := by
    simpa [prefixWord, tailWord_2971849, baseEnd_2971849] using wordTrace_append hprefix tailTrace_2971849
  have hstable : (prefixWord ++ tailWord_2971849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971849).length < 2 ^ (prefixWord ++ tailWord_2971849).sum := by decide
  have hdescent : baseEnd_2971849 < baseStart_2971849 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971859 : List Nat := [1, 1, 1, 2, 1, 1, 1, 3, 8, 4]
def baseStart_2971859 : Nat := 118140960795 + 2971859 * 2 ^ 59
def prefixEnd_2971859 : Nat := 4983230072969 + 3 ^ 40 * 2971859 * 2
def baseEnd_2971859 : Nat := 508664034796731107231725

theorem tailTrace_2971859 : CollatzResearch.WordTrace tailWord_2971859 prefixEnd_2971859 508664034796731107231725 := by
  unfold tailWord_2971859
  simp only [CollatzResearch.WordTrace]
  refine ⟨108392602540469870953942631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72261735026979913969295087 108392602540469870953942631)
  ·
    refine ⟨162588903810704806430913947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108392602540469870953942631 162588903810704806430913947)
    ·
      refine ⟨243883355716057209646370921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162588903810704806430913947 243883355716057209646370921)
      ·
        refine ⟨182912516787042907234778191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243883355716057209646370921 182912516787042907234778191)
        ·
          refine ⟨274368775180564360852167287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182912516787042907234778191 274368775180564360852167287)
          ·
            refine ⟨411553162770846541278250931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274368775180564360852167287 411553162770846541278250931)
            ·
              refine ⟨617329744156269811917376397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411553162770846541278250931 617329744156269811917376397)
              ·
                refine ⟨231498654058601179469016149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 617329744156269811917376397 231498654058601179469016149)
                ·
                  refine ⟨2712874852249232571902533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 231498654058601179469016149 2712874852249232571902533)
                  ·
                    refine ⟨508664034796731107231725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2712874852249232571902533 508664034796731107231725)
                    ·
                      rfl

theorem cell23_2971859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 8, 4].length) (baseStart_2971859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971859 prefixEnd_2971859 := by exact prefixLift 2971859
  have htrace : WordTrace (prefixWord ++ tailWord_2971859) baseStart_2971859 baseEnd_2971859 := by
    simpa [prefixWord, tailWord_2971859, baseEnd_2971859] using wordTrace_append hprefix tailTrace_2971859
  have hstable : (prefixWord ++ tailWord_2971859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971859).length < 2 ^ (prefixWord ++ tailWord_2971859).sum := by decide
  have hdescent : baseEnd_2971859 < baseStart_2971859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971866 : List Nat := [3, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4]
def baseStart_2971866 : Nat := 118140960795 + 2971866 * 2 ^ 59
def prefixEnd_2971866 : Nat := 4983230072969 + 3 ^ 40 * 2971866 * 2
def baseEnd_2971866 : Nat := 1525995698754774794307643

theorem tailTrace_2971866 : CollatzResearch.WordTrace tailWord_2971866 prefixEnd_2971866 1525995698754774794307643 := by
  unfold tailWord_2971866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27098214462861127787361863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72261905234296340766298301 27098214462861127787361863)
  ·
    refine ⟨40647321694291691681042795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27098214462861127787361863 40647321694291691681042795)
    ·
      refine ⟨60970982541437537521564193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40647321694291691681042795 60970982541437537521564193)
      ·
        refine ⟨45728236906078153141173145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60970982541437537521564193 45728236906078153141173145)
        ·
          refine ⟨34296177679558614855879859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45728236906078153141173145 34296177679558614855879859)
          ·
            refine ⟨51444266519337922283819789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34296177679558614855879859 51444266519337922283819789)
            ·
              refine ⟨19291599944751720856432421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51444266519337922283819789 19291599944751720856432421)
              ·
                refine ⟨3617174989640947660581079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19291599944751720856432421 3617174989640947660581079)
                ·
                  refine ⟨5425762484461421490871619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617174989640947660581079 5425762484461421490871619)
                  ·
                    refine ⟨8138643726692132236307429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5425762484461421490871619 8138643726692132236307429)
                    ·
                      refine ⟨1525995698754774794307643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8138643726692132236307429 1525995698754774794307643)
                      ·
                        rfl

theorem cell23_2971866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 4, 1, 1, 4].length) (baseStart_2971866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971866 prefixEnd_2971866 := by exact prefixLift 2971866
  have htrace : WordTrace (prefixWord ++ tailWord_2971866) baseStart_2971866 baseEnd_2971866 := by
    simpa [prefixWord, tailWord_2971866, baseEnd_2971866] using wordTrace_append hprefix tailTrace_2971866
  have hstable : (prefixWord ++ tailWord_2971866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971866).length < 2 ^ (prefixWord ++ tailWord_2971866).sum := by decide
  have hdescent : baseEnd_2971866 < baseStart_2971866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971877 : List Nat := [1, 3, 1, 4, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2971877 : Nat := 118140960795 + 2971877 * 2 ^ 59
def prefixEnd_2971877 : Nat := 4983230072969 + 3 ^ 40 * 2971877 * 2
def baseEnd_2971877 : Nat := 1526001347041974251270093

theorem tailTrace_2971877 : CollatzResearch.WordTrace tailWord_2971877 prefixEnd_2971877 1526001347041974251270093 := by
  unfold tailWord_2971877
  simp only [CollatzResearch.WordTrace]
  refine ⟨108393259054404660028097885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72262172702936440018731923 108393259054404660028097885)
  ·
    refine ⟨40647472145401747510536707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108393259054404660028097885 40647472145401747510536707)
    ·
      refine ⟨60971208218102621265805061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40647472145401747510536707 60971208218102621265805061)
      ·
        refine ⟨11432101540894241487338449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60971208218102621265805061 11432101540894241487338449)
        ·
          refine ⟨8574076155670681115503837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11432101540894241487338449 8574076155670681115503837)
          ·
            refine ⟨3215278558376505418313939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8574076155670681115503837 3215278558376505418313939)
            ·
              refine ⟨4822917837564758127470909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215278558376505418313939 4822917837564758127470909)
              ·
                refine ⟨1808594189086784297801591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4822917837564758127470909 1808594189086784297801591)
                ·
                  refine ⟨2712891283630176446702387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808594189086784297801591 2712891283630176446702387)
                  ·
                    refine ⟨4069336925445264670053581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2712891283630176446702387 4069336925445264670053581)
                    ·
                      refine ⟨1526001347041974251270093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069336925445264670053581 1526001347041974251270093)
                      ·
                        rfl

theorem cell23_2971877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2971877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971877 prefixEnd_2971877 := by exact prefixLift 2971877
  have htrace : WordTrace (prefixWord ++ tailWord_2971877) baseStart_2971877 baseEnd_2971877 := by
    simpa [prefixWord, tailWord_2971877, baseEnd_2971877] using wordTrace_append hprefix tailTrace_2971877
  have hstable : (prefixWord ++ tailWord_2971877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971877).length < 2 ^ (prefixWord ++ tailWord_2971877).sum := by decide
  have hdescent : baseEnd_2971877 < baseStart_2971877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971886 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3]
def baseStart_2971886 : Nat := 118140960795 + 2971886 * 2 ^ 59
def prefixEnd_2971886 : Nat := 4983230072969 + 3 ^ 40 * 2971886 * 2
def baseEnd_2971886 : Nat := 1526005968367864716057551

theorem tailTrace_2971886 : CollatzResearch.WordTrace tailWord_2971886 prefixEnd_2971886 1526005968367864716057551 := by
  unfold tailWord_2971886
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549198413921506820646939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72262391540914703043450341 13549198413921506820646939)
  ·
    refine ⟨20323797620882260230970409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13549198413921506820646939 20323797620882260230970409)
    ·
      refine ⟨15242848215661695173227807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20323797620882260230970409 15242848215661695173227807)
      ·
        refine ⟨22864272323492542759841711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15242848215661695173227807 22864272323492542759841711)
        ·
          refine ⟨34296408485238814139762567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22864272323492542759841711 34296408485238814139762567)
          ·
            refine ⟨51444612727858221209643851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34296408485238814139762567 51444612727858221209643851)
            ·
              refine ⟨77166919091787331814465777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51444612727858221209643851 77166919091787331814465777)
              ·
                refine ⟨57875189318840498860849333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77166919091787331814465777 57875189318840498860849333)
                ·
                  refine ⟨5425798998641296768204625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57875189318840498860849333 5425798998641296768204625)
                  ·
                    refine ⟨4069349248980972576153469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5425798998641296768204625 4069349248980972576153469)
                    ·
                      refine ⟨1526005968367864716057551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069349248980972576153469 1526005968367864716057551)
                      ·
                        rfl

theorem cell23_2971886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 5, 2, 3].length) (baseStart_2971886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971886 prefixEnd_2971886 := by exact prefixLift 2971886
  have htrace : WordTrace (prefixWord ++ tailWord_2971886) baseStart_2971886 baseEnd_2971886 := by
    simpa [prefixWord, tailWord_2971886, baseEnd_2971886] using wordTrace_append hprefix tailTrace_2971886
  have hstable : (prefixWord ++ tailWord_2971886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971886).length < 2 ^ (prefixWord ++ tailWord_2971886).sum := by decide
  have hdescent : baseEnd_2971886 < baseStart_2971886 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971900 : List Nat := [2, 2, 2, 1, 4, 1, 3, 1, 3, 2, 2]
def baseStart_2971900 : Nat := 118140960795 + 2971900 * 2 ^ 59
def prefixEnd_2971900 : Nat := 4983230072969 + 3 ^ 40 * 2971900 * 2
def baseEnd_2971900 : Nat := 1526013157097027661282487

theorem tailTrace_2971900 : CollatzResearch.WordTrace tailWord_2971900 prefixEnd_2971900 1526013157097027661282487 := by
  unfold tailWord_2971900
  simp only [CollatzResearch.WordTrace]
  refine ⟨54197048966660667478092577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72262731955547556637456769 54197048966660667478092577)
  ·
    refine ⟨40647786724995500608569433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54197048966660667478092577 40647786724995500608569433)
    ·
      refine ⟨30485840043746625456427075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40647786724995500608569433 30485840043746625456427075)
      ·
        refine ⟨45728760065619938184640613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30485840043746625456427075 45728760065619938184640613)
        ·
          refine ⟨8574142512303738409620115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45728760065619938184640613 8574142512303738409620115)
          ·
            refine ⟨12861213768455607614430173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574142512303738409620115 12861213768455607614430173)
            ·
              refine ⟨4822955163170852855411315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12861213768455607614430173 4822955163170852855411315)
              ·
                refine ⟨7234432744756279283116973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4822955163170852855411315 7234432744756279283116973)
                ·
                  refine ⟨2712912279283604731168865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7234432744756279283116973 2712912279283604731168865)
                  ·
                    refine ⟨2034684209462703548376649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712912279283604731168865 2034684209462703548376649)
                    ·
                      refine ⟨1526013157097027661282487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034684209462703548376649 1526013157097027661282487)
                      ·
                        rfl

theorem cell23_2971900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 2, 2].length) (baseStart_2971900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971900 prefixEnd_2971900 := by exact prefixLift 2971900
  have htrace : WordTrace (prefixWord ++ tailWord_2971900) baseStart_2971900 baseEnd_2971900 := by
    simpa [prefixWord, tailWord_2971900, baseEnd_2971900] using wordTrace_append hprefix tailTrace_2971900
  have hstable : (prefixWord ++ tailWord_2971900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971900).length < 2 ^ (prefixWord ++ tailWord_2971900).sum := by decide
  have hdescent : baseEnd_2971900 < baseStart_2971900 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971906 : List Nat := [3, 4, 1, 1, 2, 1, 1, 10]
def baseStart_2971906 : Nat := 118140960795 + 2971906 * 2 ^ 59
def prefixEnd_2971906 : Nat := 4983230072969 + 3 ^ 40 * 2971906 * 2
def baseEnd_2971906 : Nat := 56519119925220542141017

theorem tailTrace_2971906 : CollatzResearch.WordTrace tailWord_2971906 prefixEnd_2971906 56519119925220542141017 := by
  unfold tailWord_2971906
  simp only [CollatzResearch.WordTrace]
  refine ⟨27098579192824899495225893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72262877847533065320602381 27098579192824899495225893)
  ·
    refine ⟨5080983598654668655354855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27098579192824899495225893 5080983598654668655354855)
    ·
      refine ⟨7621475397982002983032283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5080983598654668655354855 7621475397982002983032283)
      ·
        refine ⟨11432213096973004474548425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7621475397982002983032283 11432213096973004474548425)
        ·
          refine ⟨8574159822729753355911319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11432213096973004474548425 8574159822729753355911319)
          ·
            refine ⟨12861239734094630033866979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574159822729753355911319 12861239734094630033866979)
            ·
              refine ⟨19291859601141945050800469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12861239734094630033866979 19291859601141945050800469)
              ·
                refine ⟨56519119925220542141017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 19291859601141945050800469 56519119925220542141017)
                ·
                  rfl

theorem cell23_2971906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 10].length) (baseStart_2971906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971906 prefixEnd_2971906 := by exact prefixLift 2971906
  have htrace : WordTrace (prefixWord ++ tailWord_2971906) baseStart_2971906 baseEnd_2971906 := by
    simpa [prefixWord, tailWord_2971906, baseEnd_2971906] using wordTrace_append hprefix tailTrace_2971906
  have hstable : (prefixWord ++ tailWord_2971906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971906).length < 2 ^ (prefixWord ++ tailWord_2971906).sum := by decide
  have hdescent : baseEnd_2971906 < baseStart_2971906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971916 : List Nat := [2, 2, 1, 2, 2, 2, 2, 3, 1, 3, 3]
def baseStart_2971916 : Nat := 118140960795 + 2971916 * 2 ^ 59
def prefixEnd_2971916 : Nat := 4983230072969 + 3 ^ 40 * 2971916 * 2
def baseEnd_2971916 : Nat := 1526021372787499598682413

theorem tailTrace_2971916 : CollatzResearch.WordTrace tailWord_2971916 prefixEnd_2971916 1526021372787499598682413 := by
  unfold tailWord_2971916
  simp only [CollatzResearch.WordTrace]
  refine ⟨54197340750631684844383801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72263121000842246459178401 54197340750631684844383801)
  ·
    refine ⟨40648005562973763633287851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54197340750631684844383801 40648005562973763633287851)
    ·
      refine ⟨60972008344460645449931777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40648005562973763633287851 60972008344460645449931777)
      ·
        refine ⟨45729006258345484087448833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60972008344460645449931777 45729006258345484087448833)
        ·
          refine ⟨34296754693759113065586625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45729006258345484087448833 34296754693759113065586625)
          ·
            refine ⟨25722566020319334799189969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34296754693759113065586625 25722566020319334799189969)
            ·
              refine ⟨19291924515239501099392477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25722566020319334799189969 19291924515239501099392477)
              ·
                refine ⟨7234471693214812912272179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19291924515239501099392477 7234471693214812912272179)
                ·
                  refine ⟨10851707539822219368408269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7234471693214812912272179 10851707539822219368408269)
                  ·
                    refine ⟨4069390327433332263153101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10851707539822219368408269 4069390327433332263153101)
                    ·
                      refine ⟨1526021372787499598682413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069390327433332263153101 1526021372787499598682413)
                      ·
                        rfl

theorem cell23_2971916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 3, 1, 3, 3].length) (baseStart_2971916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971916 prefixEnd_2971916 := by exact prefixLift 2971916
  have htrace : WordTrace (prefixWord ++ tailWord_2971916) baseStart_2971916 baseEnd_2971916 := by
    simpa [prefixWord, tailWord_2971916, baseEnd_2971916] using wordTrace_append hprefix tailTrace_2971916
  have hstable : (prefixWord ++ tailWord_2971916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971916).length < 2 ^ (prefixWord ++ tailWord_2971916).sum := by decide
  have hdescent : baseEnd_2971916 < baseStart_2971916 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971959 : List Nat := [1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5]
def baseStart_2971959 : Nat := 118140960795 + 2971959 * 2 ^ 59
def prefixEnd_2971959 : Nat := 4983230072969 + 3 ^ 40 * 2971959 * 2
def baseEnd_2971959 : Nat := 1526043452455642930444715

theorem tailTrace_2971959 : CollatzResearch.WordTrace tailWord_2971959 prefixEnd_2971959 1526043452455642930444715 := by
  unfold tailWord_2971959
  simp only [CollatzResearch.WordTrace]
  refine ⟨108396249840107588032582931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72264166560071725355055287 108396249840107588032582931)
  ·
    refine ⟨162594374760161382048874397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108396249840107588032582931 162594374760161382048874397)
    ·
      refine ⟨60972890535060518268327899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162594374760161382048874397 60972890535060518268327899)
      ·
        refine ⟨91459335802590777402491849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60972890535060518268327899 91459335802590777402491849)
        ·
          refine ⟨68594501851943083051868887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91459335802590777402491849 68594501851943083051868887)
          ·
            refine ⟨102891752777914624577803331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68594501851943083051868887 102891752777914624577803331)
            ·
              refine ⟨154337629166871936866704997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102891752777914624577803331 154337629166871936866704997)
              ·
                refine ⟨28938305468788488162507187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 154337629166871936866704997 28938305468788488162507187)
                ·
                  refine ⟨43407458203182732243760781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28938305468788488162507187 43407458203182732243760781)
                  ·
                    refine ⟨16277796826193524591410293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43407458203182732243760781 16277796826193524591410293)
                    ·
                      refine ⟨1526043452455642930444715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16277796826193524591410293 1526043452455642930444715)
                      ·
                        rfl

theorem cell23_2971959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_2971959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971959 prefixEnd_2971959 := by exact prefixLift 2971959
  have htrace : WordTrace (prefixWord ++ tailWord_2971959) baseStart_2971959 baseEnd_2971959 := by
    simpa [prefixWord, tailWord_2971959, baseEnd_2971959] using wordTrace_append hprefix tailTrace_2971959
  have hstable : (prefixWord ++ tailWord_2971959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971959).length < 2 ^ (prefixWord ++ tailWord_2971959).sum := by decide
  have hdescent : baseEnd_2971959 < baseStart_2971959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971966 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 1, 8]
def baseStart_2971966 : Nat := 118140960795 + 2971966 * 2 ^ 59
def prefixEnd_2971966 : Nat := 4983230072969 + 3 ^ 40 * 2971966 * 2
def baseEnd_2971966 : Nat := 508682348940074801019061

theorem tailTrace_2971966 : CollatzResearch.WordTrace tailWord_2971966 prefixEnd_2971966 508682348940074801019061 := by
  unfold tailWord_2971966
  simp only [CollatzResearch.WordTrace]
  refine ⟨13549563143885278528510969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72264336767388152152058501 13549563143885278528510969)
  ·
    refine ⟨10162172357913958896383227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13549563143885278528510969 10162172357913958896383227)
    ·
      refine ⟨15243258536870938344574841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162172357913958896383227 15243258536870938344574841)
      ·
        refine ⟨11432443902653203758431131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15243258536870938344574841 11432443902653203758431131)
        ·
          refine ⟨17148665853979805637646697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432443902653203758431131 17148665853979805637646697)
          ·
            refine ⟨12861499390484854228235023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17148665853979805637646697 12861499390484854228235023)
            ·
              refine ⟨19292249085727281342352535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12861499390484854228235023 19292249085727281342352535)
              ·
                refine ⟨28938373628590922013528803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19292249085727281342352535 28938373628590922013528803)
                ·
                  refine ⟨43407560442886383020293205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28938373628590922013528803 43407560442886383020293205)
                  ·
                    refine ⟨508682348940074801019061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 43407560442886383020293205 508682348940074801019061)
                    ·
                      rfl

theorem cell23_2971966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 1, 8].length) (baseStart_2971966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971966 prefixEnd_2971966 := by exact prefixLift 2971966
  have htrace : WordTrace (prefixWord ++ tailWord_2971966) baseStart_2971966 baseEnd_2971966 := by
    simpa [prefixWord, tailWord_2971966, baseEnd_2971966] using wordTrace_append hprefix tailTrace_2971966
  have hstable : (prefixWord ++ tailWord_2971966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971966).length < 2 ^ (prefixWord ++ tailWord_2971966).sum := by decide
  have hdescent : baseEnd_2971966 < baseStart_2971966 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2971973 : List Nat := [1, 3, 1, 1, 1, 2, 1, 1, 8, 2, 2]
def baseStart_2971973 : Nat := 118140960795 + 2971973 * 2 ^ 59
def prefixEnd_2971973 : Nat := 4983230072969 + 3 ^ 40 * 2971973 * 2
def baseEnd_2971973 : Nat := 1526050641184805875669651

theorem tailTrace_2971973 : CollatzResearch.WordTrace tailWord_2971973 prefixEnd_2971973 1526050641184805875669651 := by
  unfold tailWord_2971973
  simp only [CollatzResearch.WordTrace]
  refine ⟨108396760462056868423592573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72264506974704578949061715 108396760462056868423592573)
  ·
    refine ⟨40648785173271325658847215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108396760462056868423592573 40648785173271325658847215)
    ·
      refine ⟨60973177759906988488270823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40648785173271325658847215 60973177759906988488270823)
      ·
        refine ⟨91459766639860482732406235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60973177759906988488270823 91459766639860482732406235)
        ·
          refine ⟨137189649959790724098609353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91459766639860482732406235 137189649959790724098609353)
          ·
            refine ⟨102892237469843043073957015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137189649959790724098609353 102892237469843043073957015)
            ·
              refine ⟨154338356204764564610935523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102892237469843043073957015 154338356204764564610935523)
              ·
                refine ⟨231507534307146846916403285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154338356204764564610935523 231507534307146846916403285)
                ·
                  refine ⟨2712978917661877112301601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 231507534307146846916403285 2712978917661877112301601)
                  ·
                    refine ⟨2034734188246407834226201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2712978917661877112301601 2034734188246407834226201)
                    ·
                      refine ⟨1526050641184805875669651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034734188246407834226201 1526050641184805875669651)
                      ·
                        rfl

theorem cell23_2971973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 1, 8, 2, 2].length) (baseStart_2971973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2971973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2971973 prefixEnd_2971973 := by exact prefixLift 2971973
  have htrace : WordTrace (prefixWord ++ tailWord_2971973) baseStart_2971973 baseEnd_2971973 := by
    simpa [prefixWord, tailWord_2971973, baseEnd_2971973] using wordTrace_append hprefix tailTrace_2971973
  have hstable : (prefixWord ++ tailWord_2971973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2971973).length < 2 ^ (prefixWord ++ tailWord_2971973).sum := by decide
  have hdescent : baseEnd_2971973 < baseStart_2971973 := by decide
  rcases family_descends (prefixWord ++ tailWord_2971973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972007 : List Nat := [1, 1, 5, 1, 3, 1, 3, 2, 2, 2, 2]
def baseStart_2972007 : Nat := 118140960795 + 2972007 * 2 ^ 59
def prefixEnd_2972007 : Nat := 4983230072969 + 3 ^ 40 * 2972007 * 2
def baseEnd_2972007 : Nat := 1526068099527058742644495

theorem tailTrace_2972007 : CollatzResearch.WordTrace tailWord_2972007 prefixEnd_2972007 1526068099527058742644495 := by
  unfold tailWord_2972007
  simp only [CollatzResearch.WordTrace]
  refine ⟨108398000543933692230330275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72265333695955794820220183 108398000543933692230330275)
  ·
    refine ⟨162597000815900538345495413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108398000543933692230330275 162597000815900538345495413)
    ·
      refine ⟨15243468826490675469890195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 162597000815900538345495413 15243468826490675469890195)
      ·
        refine ⟨22865203239736013204835293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15243468826490675469890195 22865203239736013204835293)
        ·
          refine ⟨8574451214901004951813235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22865203239736013204835293 8574451214901004951813235)
          ·
            refine ⟨12861676822351507427719853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574451214901004951813235 12861676822351507427719853)
            ·
              refine ⟨4823128808381815285394945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12861676822351507427719853 4823128808381815285394945)
              ·
                refine ⟨3617346606286361464046209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823128808381815285394945 3617346606286361464046209)
                ·
                  refine ⟨2713009954714771098034657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3617346606286361464046209 2713009954714771098034657)
                  ·
                    refine ⟨2034757466036078323525993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713009954714771098034657 2034757466036078323525993)
                    ·
                      refine ⟨1526068099527058742644495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034757466036078323525993 1526068099527058742644495)
                      ·
                        rfl

theorem cell23_2972007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3, 2, 2, 2, 2].length) (baseStart_2972007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972007 prefixEnd_2972007 := by exact prefixLift 2972007
  have htrace : WordTrace (prefixWord ++ tailWord_2972007) baseStart_2972007 baseEnd_2972007 := by
    simpa [prefixWord, tailWord_2972007, baseEnd_2972007] using wordTrace_append hprefix tailTrace_2972007
  have hstable : (prefixWord ++ tailWord_2972007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972007).length < 2 ^ (prefixWord ++ tailWord_2972007).sum := by decide
  have hdescent : baseEnd_2972007 < baseStart_2972007 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972013 : List Nat := [1, 5, 1, 1, 1, 2, 1, 6, 5]
def baseStart_2972013 : Nat := 118140960795 + 2972013 * 2 ^ 59
def prefixEnd_2972013 : Nat := 4983230072969 + 3 ^ 40 * 2972013 * 2
def baseEnd_2972013 : Nat := 169563464490109524352163

theorem tailTrace_2972013 : CollatzResearch.WordTrace tailWord_2972013 prefixEnd_2972013 169563464490109524352163 := by
  unfold tailWord_2972013
  simp only [CollatzResearch.WordTrace]
  refine ⟨108398219381911955255048693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72265479587941303503365795 108398219381911955255048693)
  ·
    refine ⟨10162333067054245805160815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108398219381911955255048693 10162333067054245805160815)
    ·
      refine ⟨15243499600581368707741223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162333067054245805160815 15243499600581368707741223)
      ·
        refine ⟨22865249400872053061611835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15243499600581368707741223 22865249400872053061611835)
        ·
          refine ⟨34297874101308079592417753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22865249400872053061611835 34297874101308079592417753)
          ·
            refine ⟨25723405575981059694313315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34297874101308079592417753 25723405575981059694313315)
            ·
              refine ⟨38585108363971589541469973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25723405575981059694313315 38585108363971589541469973)
              ·
                refine ⟨1808676954561168259756405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38585108363971589541469973 1808676954561168259756405)
                ·
                  refine ⟨169563464490109524352163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1808676954561168259756405 169563464490109524352163)
                  ·
                    rfl

theorem cell23_2972013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 6, 5].length) (baseStart_2972013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972013 prefixEnd_2972013 := by exact prefixLift 2972013
  have htrace : WordTrace (prefixWord ++ tailWord_2972013) baseStart_2972013 baseEnd_2972013 := by
    simpa [prefixWord, tailWord_2972013, baseEnd_2972013] using wordTrace_append hprefix tailTrace_2972013
  have hstable : (prefixWord ++ tailWord_2972013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972013).length < 2 ^ (prefixWord ++ tailWord_2972013).sum := by decide
  have hdescent : baseEnd_2972013 < baseStart_2972013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972063 : List Nat := [1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4]
def baseStart_2972063 : Nat := 118140960795 + 2972063 * 2 ^ 59
def prefixEnd_2972063 : Nat := 4983230072969 + 3 ^ 40 * 2972063 * 2
def baseEnd_2972063 : Nat := 1526096854443710523544237

theorem tailTrace_2972063 : CollatzResearch.WordTrace tailWord_2972063 prefixEnd_2972063 1526096854443710523544237 := by
  unfold tailWord_2972063
  simp only [CollatzResearch.WordTrace]
  refine ⟨108400043031730813794368843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72266695354487209196245895 108400043031730813794368843)
  ·
    refine ⟨162600064547596220691553265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108400043031730813794368843 162600064547596220691553265)
    ·
      refine ⟨121950048410697165518664949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162600064547596220691553265 121950048410697165518664949)
      ·
        refine ⟨11432817038502859267374839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 121950048410697165518664949 11432817038502859267374839)
        ·
          refine ⟨17149225557754288901062259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11432817038502859267374839 17149225557754288901062259)
          ·
            refine ⟨25723838336631433351593389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17149225557754288901062259 25723838336631433351593389)
            ·
              refine ⟨9646439376236787506847521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25723838336631433351593389 9646439376236787506847521)
              ·
                refine ⟨7234829532177590630135641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9646439376236787506847521 7234829532177590630135641)
                ·
                  refine ⟨5426122149133192972601731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7234829532177590630135641 5426122149133192972601731)
                  ·
                    refine ⟨8139183223699789458902597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426122149133192972601731 8139183223699789458902597)
                    ·
                      refine ⟨1526096854443710523544237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8139183223699789458902597 1526096854443710523544237)
                      ·
                        rfl

theorem cell23_2972063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 4].length) (baseStart_2972063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972063 prefixEnd_2972063 := by exact prefixLift 2972063
  have htrace : WordTrace (prefixWord ++ tailWord_2972063) baseStart_2972063 baseEnd_2972063 := by
    simpa [prefixWord, tailWord_2972063, baseEnd_2972063] using wordTrace_append hprefix tailTrace_2972063
  have hstable : (prefixWord ++ tailWord_2972063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972063).length < 2 ^ (prefixWord ++ tailWord_2972063).sum := by decide
  have hdescent : baseEnd_2972063 < baseStart_2972063 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972150 : List Nat := [5, 1, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_2972150 : Nat := 118140960795 + 2972150 * 2 ^ 59
def prefixEnd_2972150 : Nat := 4983230072969 + 3 ^ 40 * 2972150 * 2
def baseEnd_2972150 : Nat := 508713842420217227718779

theorem tailTrace_2972150 : CollatzResearch.WordTrace tailWord_2972150 prefixEnd_2972150 508713842420217227718779 := by
  unfold tailWord_2972150
  simp only [CollatzResearch.WordTrace]
  refine ⟨6775201011400976728299119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72268810788277085101857269 6775201011400976728299119)
  ·
    refine ⟨10162801517101465092448679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6775201011400976728299119 10162801517101465092448679)
    ·
      refine ⟨15244202275652197638673019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10162801517101465092448679 15244202275652197638673019)
      ·
        refine ⟨22866303413478296458009529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15244202275652197638673019 22866303413478296458009529)
        ·
          refine ⟨17149727560108722343507147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22866303413478296458009529 17149727560108722343507147)
          ·
            refine ⟨25724591340163083515260721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17149727560108722343507147 25724591340163083515260721)
            ·
              refine ⟨19293443505122312636445541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25724591340163083515260721 19293443505122312636445541)
              ·
                refine ⟨3617520657210433619333539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19293443505122312636445541 3617520657210433619333539)
                ·
                  refine ⟨5426280985815650429000309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617520657210433619333539 5426280985815650429000309)
                  ·
                    refine ⟨508713842420217227718779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5426280985815650429000309 508713842420217227718779)
                    ·
                      rfl

theorem cell23_2972150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_2972150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972150 prefixEnd_2972150 := by exact prefixLift 2972150
  have htrace : WordTrace (prefixWord ++ tailWord_2972150) baseStart_2972150 baseEnd_2972150 := by
    simpa [prefixWord, tailWord_2972150, baseEnd_2972150] using wordTrace_append hprefix tailTrace_2972150
  have hstable : (prefixWord ++ tailWord_2972150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972150).length < 2 ^ (prefixWord ++ tailWord_2972150).sum := by decide
  have hdescent : baseEnd_2972150 < baseStart_2972150 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972153 : List Nat := [1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 4]
def baseStart_2972153 : Nat := 118140960795 + 2972153 * 2 ^ 59
def prefixEnd_2972153 : Nat := 4983230072969 + 3 ^ 40 * 2972153 * 2
def baseEnd_2972153 : Nat := 1526143067702615171418823

theorem tailTrace_2972153 : CollatzResearch.WordTrace tailWord_2972153 prefixEnd_2972153 1526143067702615171418823 := by
  unfold tailWord_2972153
  simp only [CollatzResearch.WordTrace]
  refine ⟨108403325601404759165145113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72268883734269839443430075 108403325601404759165145113)
  ·
    refine ⟨81302494201053569373858835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108403325601404759165145113 81302494201053569373858835)
    ·
      refine ⟨121953741301580354060788253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81302494201053569373858835 121953741301580354060788253)
      ·
        refine ⟨45732652988092632772795595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121953741301580354060788253 45732652988092632772795595)
        ·
          refine ⟨68598979482138949159193393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45732652988092632772795595 68598979482138949159193393)
          ·
            refine ⟨51449234611604211869395045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68598979482138949159193393 51449234611604211869395045)
            ·
              refine ⟨9646731489675789725511571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51449234611604211869395045 9646731489675789725511571)
              ·
                refine ⟨14470097234513684588267357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9646731489675789725511571 14470097234513684588267357)
                ·
                  refine ⟨5426286462942631720600259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14470097234513684588267357 5426286462942631720600259)
                  ·
                    refine ⟨8139429694413947580900389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426286462942631720600259 8139429694413947580900389)
                    ·
                      refine ⟨1526143067702615171418823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8139429694413947580900389 1526143067702615171418823)
                      ·
                        rfl

theorem cell23_2972153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 1, 3, 1, 4].length) (baseStart_2972153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972153 prefixEnd_2972153 := by exact prefixLift 2972153
  have htrace : WordTrace (prefixWord ++ tailWord_2972153) baseStart_2972153 baseEnd_2972153 := by
    simpa [prefixWord, tailWord_2972153, baseEnd_2972153] using wordTrace_append hprefix tailTrace_2972153
  have hstable : (prefixWord ++ tailWord_2972153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972153).length < 2 ^ (prefixWord ++ tailWord_2972153).sum := by decide
  have hdescent : baseEnd_2972153 < baseStart_2972153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972163 : List Nat := [1, 1, 1, 3, 2, 1, 4, 2, 4, 4]
def baseStart_2972163 : Nat := 118140960795 + 2972163 * 2 ^ 59
def prefixEnd_2972163 : Nat := 4983230072969 + 3 ^ 40 * 2972163 * 2
def baseEnd_2972163 : Nat := 508716067503053377431259

theorem tailTrace_2972163 : CollatzResearch.WordTrace tailWord_2972163 prefixEnd_2972163 508716067503053377431259 := by
  unfold tailWord_2972163
  simp only [CollatzResearch.WordTrace]
  refine ⟨108403690331368530873009143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72269126887579020582006095 108403690331368530873009143)
  ·
    refine ⟨162605535497052796309513715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108403690331368530873009143 162605535497052796309513715)
    ·
      refine ⟨243908303245579194464270573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162605535497052796309513715 243908303245579194464270573)
      ·
        refine ⟨91465613717092197924101465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243908303245579194464270573 91465613717092197924101465)
        ·
          refine ⟨68599210287819148443076099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91465613717092197924101465 68599210287819148443076099)
          ·
            refine ⟨102898815431728722664614149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68599210287819148443076099 102898815431728722664614149)
            ·
              refine ⟨19293527893449135499615153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102898815431728722664614149 19293527893449135499615153)
              ·
                refine ⟨14470145920086851624711365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19293527893449135499615153 14470145920086851624711365)
                ·
                  refine ⟨2713152360016284679633381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14470145920086851624711365 2713152360016284679633381)
                  ·
                    refine ⟨508716067503053377431259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2713152360016284679633381 508716067503053377431259)
                    ·
                      rfl

theorem cell23_2972163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 2, 4, 4].length) (baseStart_2972163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972163 prefixEnd_2972163 := by exact prefixLift 2972163
  have htrace : WordTrace (prefixWord ++ tailWord_2972163) baseStart_2972163 baseEnd_2972163 := by
    simpa [prefixWord, tailWord_2972163, baseEnd_2972163] using wordTrace_append hprefix tailTrace_2972163
  have hstable : (prefixWord ++ tailWord_2972163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972163).length < 2 ^ (prefixWord ++ tailWord_2972163).sum := by decide
  have hdescent : baseEnd_2972163 < baseStart_2972163 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972164 : List Nat := [2, 3, 2, 3, 1, 1, 1, 5, 1, 1, 3]
def baseStart_2972164 : Nat := 118140960795 + 2972164 * 2 ^ 59
def prefixEnd_2972164 : Nat := 4983230072969 + 3 ^ 40 * 2972164 * 2
def baseEnd_2972164 : Nat := 1526148715989814628381273

theorem tailTrace_2972164 : CollatzResearch.WordTrace tailWord_2972164 prefixEnd_2972164 1526148715989814628381273 := by
  unfold tailWord_2972164
  simp only [CollatzResearch.WordTrace]
  refine ⟨54201863402182454021897773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72269151202909938695863697 54201863402182454021897773)
  ·
    refine ⟨20325698775818420258211665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54201863402182454021897773 20325698775818420258211665)
    ·
      refine ⟨15244274081863815193658749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20325698775818420258211665 15244274081863815193658749)
      ·
        refine ⟨5716602780698930697622031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15244274081863815193658749 5716602780698930697622031)
        ·
          refine ⟨8574904171048396046433047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716602780698930697622031 8574904171048396046433047)
          ·
            refine ⟨12862356256572594069649571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8574904171048396046433047 12862356256572594069649571)
            ·
              refine ⟨19293534384858891104474357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12862356256572594069649571 19293534384858891104474357)
              ·
                refine ⟨1808768848580521041044471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19293534384858891104474357 1808768848580521041044471)
                ·
                  refine ⟨2713153272870781561566707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808768848580521041044471 2713153272870781561566707)
                  ·
                    refine ⟨4069729909306172342350061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713153272870781561566707 4069729909306172342350061)
                    ·
                      refine ⟨1526148715989814628381273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069729909306172342350061 1526148715989814628381273)
                      ·
                        rfl

theorem cell23_2972164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 1, 5, 1, 1, 3].length) (baseStart_2972164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972164 prefixEnd_2972164 := by exact prefixLift 2972164
  have htrace : WordTrace (prefixWord ++ tailWord_2972164) baseStart_2972164 baseEnd_2972164 := by
    simpa [prefixWord, tailWord_2972164, baseEnd_2972164] using wordTrace_append hprefix tailTrace_2972164
  have hstable : (prefixWord ++ tailWord_2972164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972164).length < 2 ^ (prefixWord ++ tailWord_2972164).sum := by decide
  have hdescent : baseEnd_2972164 < baseStart_2972164 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972170 : List Nat := [3, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4]
def baseStart_2972170 : Nat := 118140960795 + 2972170 * 2 ^ 59
def prefixEnd_2972170 : Nat := 4983230072969 + 3 ^ 40 * 2972170 * 2
def baseEnd_2972170 : Nat := 1526151796873741604906245

theorem tailTrace_2972170 : CollatzResearch.WordTrace tailWord_2972170 prefixEnd_2972170 1526151796873741604906245 := by
  unfold tailWord_2972170
  simp only [CollatzResearch.WordTrace]
  refine ⟨27100986410585792767128491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72269297094895447379009309 27100986410585792767128491)
  ·
    refine ⟨40651479615878689150692737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27100986410585792767128491 40651479615878689150692737)
    ·
      refine ⟨30488609711909016863019553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40651479615878689150692737 30488609711909016863019553)
      ·
        refine ⟨22866457283931762647264665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30488609711909016863019553 22866457283931762647264665)
        ·
          refine ⟨17149842962948821985448499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22866457283931762647264665 17149842962948821985448499)
          ·
            refine ⟨25724764444423232978172749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17149842962948821985448499 25724764444423232978172749)
            ·
              refine ⟨9646786666658712366814781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25724764444423232978172749 9646786666658712366814781)
              ·
                refine ⟨3617544999997017137555543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9646786666658712366814781 3617544999997017137555543)
                ·
                  refine ⟨5426317499995525706333315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617544999997017137555543 5426317499995525706333315)
                  ·
                    refine ⟨8139476249993288559499973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426317499995525706333315 8139476249993288559499973)
                    ·
                      refine ⟨1526151796873741604906245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8139476249993288559499973 1526151796873741604906245)
                      ·
                        rfl

theorem cell23_2972170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 3, 3, 1, 1, 4].length) (baseStart_2972170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972170 prefixEnd_2972170 := by exact prefixLift 2972170
  have htrace : WordTrace (prefixWord ++ tailWord_2972170) baseStart_2972170 baseEnd_2972170 := by
    simpa [prefixWord, tailWord_2972170, baseEnd_2972170] using wordTrace_append hprefix tailTrace_2972170
  have hstable : (prefixWord ++ tailWord_2972170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972170).length < 2 ^ (prefixWord ++ tailWord_2972170).sum := by decide
  have hdescent : baseEnd_2972170 < baseStart_2972170 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972200 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6]
def baseStart_2972200 : Nat := 118140960795 + 2972200 * 2 ^ 59
def prefixEnd_2972200 : Nat := 4983230072969 + 3 ^ 40 * 2972200 * 2
def baseEnd_2972200 : Nat := 1526167201293376487531107

theorem tailTrace_2972200 : CollatzResearch.WordTrace tailWord_2972200 prefixEnd_2972200 1526167201293376487531107 := by
  unfold tailWord_2972200
  simp only [CollatzResearch.WordTrace]
  refine ⟨54202519916117243096053027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72270026554822990794737369 54202519916117243096053027)
  ·
    refine ⟨81303779874175864644079541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54202519916117243096053027 81303779874175864644079541)
    ·
      refine ⟨7622229363203987310382457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81303779874175864644079541 7622229363203987310382457)
      ·
        refine ⟨5716672022402990482786843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7622229363203987310382457 5716672022402990482786843)
        ·
          refine ⟨8575008033604485724180265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716672022402990482786843 8575008033604485724180265)
          ·
            refine ⟨6431256025203364293135199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8575008033604485724180265 6431256025203364293135199)
            ·
              refine ⟨9646884037805046439702799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6431256025203364293135199 9646884037805046439702799)
              ·
                refine ⟨14470326056707569659554199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9646884037805046439702799 14470326056707569659554199)
                ·
                  refine ⟨21705489085061354489331299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14470326056707569659554199 21705489085061354489331299)
                  ·
                    refine ⟨32558233627592031733996949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21705489085061354489331299 32558233627592031733996949)
                    ·
                      refine ⟨1526167201293376487531107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32558233627592031733996949 1526167201293376487531107)
                      ·
                        rfl

theorem cell23_2972200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 1, 1, 6].length) (baseStart_2972200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972200 prefixEnd_2972200 := by exact prefixLift 2972200
  have htrace : WordTrace (prefixWord ++ tailWord_2972200) baseStart_2972200 baseEnd_2972200 := by
    simpa [prefixWord, tailWord_2972200, baseEnd_2972200] using wordTrace_append hprefix tailTrace_2972200
  have hstable : (prefixWord ++ tailWord_2972200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972200).length < 2 ^ (prefixWord ++ tailWord_2972200).sum := by decide
  have hdescent : baseEnd_2972200 < baseStart_2972200 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972221 : List Nat := [1, 4, 1, 3, 2, 1, 3, 3, 1, 2, 2]
def baseStart_2972221 : Nat := 118140960795 + 2972221 * 2 ^ 59
def prefixEnd_2972221 : Nat := 4983230072969 + 3 ^ 40 * 2972221 * 2
def baseEnd_2972221 : Nat := 1526177984387120905368511

theorem tailTrace_2972221 : CollatzResearch.WordTrace tailWord_2972221 prefixEnd_2972221 1526177984387120905368511 := by
  unfold tailWord_2972221
  simp only [CollatzResearch.WordTrace]
  refine ⟨108405805765158406778620517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72270537176772271185747011 108405805765158406778620517)
  ·
    refine ⟨20326088580967201270991347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108405805765158406778620517 20326088580967201270991347)
    ·
      refine ⟨30489132871450801906487021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20326088580967201270991347 30489132871450801906487021)
      ·
        refine ⟨11433424826794050714932633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30489132871450801906487021 11433424826794050714932633)
        ·
          refine ⟨8575068620095538036199475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11433424826794050714932633 8575068620095538036199475)
          ·
            refine ⟨12862602930143307054299213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575068620095538036199475 12862602930143307054299213)
            ·
              refine ⟨4823476098803740145362205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12862602930143307054299213 4823476098803740145362205)
              ·
                refine ⟨1808803537051402554510827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4823476098803740145362205 1808803537051402554510827)
                ·
                  refine ⟨2713205305577103831766241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1808803537051402554510827 2713205305577103831766241)
                  ·
                    refine ⟨2034903979182827873824681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713205305577103831766241 2034903979182827873824681)
                    ·
                      refine ⟨1526177984387120905368511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034903979182827873824681 1526177984387120905368511)
                      ·
                        rfl

theorem cell23_2972221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 2, 2].length) (baseStart_2972221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972221 prefixEnd_2972221 := by exact prefixLift 2972221
  have htrace : WordTrace (prefixWord ++ tailWord_2972221) baseStart_2972221 baseEnd_2972221 := by
    simpa [prefixWord, tailWord_2972221, baseEnd_2972221] using wordTrace_append hprefix tailTrace_2972221
  have hstable : (prefixWord ++ tailWord_2972221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972221).length < 2 ^ (prefixWord ++ tailWord_2972221).sum := by decide
  have hdescent : baseEnd_2972221 < baseStart_2972221 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972258 : List Nat := [3, 3, 2, 3, 2, 1, 1, 2, 1, 2, 3]
def baseStart_2972258 : Nat := 118140960795 + 2972258 * 2 ^ 59
def prefixEnd_2972258 : Nat := 4983230072969 + 3 ^ 40 * 2972258 * 2
def baseEnd_2972258 : Nat := 1526196983171337260605841

theorem tailTrace_2972258 : CollatzResearch.WordTrace tailWord_2972258 prefixEnd_2972258 1526196983171337260605841 := by
  unfold tailWord_2972258
  simp only [CollatzResearch.WordTrace]
  refine ⟨27101788816506090524429357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72271436844016241398478285 27101788816506090524429357)
  ·
    refine ⟨10163170806189783946661009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27101788816506090524429357 10163170806189783946661009)
    ·
      refine ⟨7622378104642337959995757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10163170806189783946661009 7622378104642337959995757)
      ·
        refine ⟨2858391789240876734998409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7622378104642337959995757 2858391789240876734998409)
        ·
          refine ⟨2143793841930657551248807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2858391789240876734998409 2143793841930657551248807)
          ·
            refine ⟨3215690762895986326873211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2143793841930657551248807 3215690762895986326873211)
            ·
              refine ⟨4823536144343979490309817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3215690762895986326873211 4823536144343979490309817)
              ·
                refine ⟨3617652108257984617732363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4823536144343979490309817 3617652108257984617732363)
                ·
                  refine ⟨5426478162386976926598545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617652108257984617732363 5426478162386976926598545)
                  ·
                    refine ⟨4069858621790232694948909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5426478162386976926598545 4069858621790232694948909)
                    ·
                      refine ⟨1526196983171337260605841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4069858621790232694948909 1526196983171337260605841)
                      ·
                        rfl

theorem cell23_2972258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 2, 1, 2, 3].length) (baseStart_2972258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972258 prefixEnd_2972258 := by exact prefixLift 2972258
  have htrace : WordTrace (prefixWord ++ tailWord_2972258) baseStart_2972258 baseEnd_2972258 := by
    simpa [prefixWord, tailWord_2972258, baseEnd_2972258] using wordTrace_append hprefix tailTrace_2972258
  have hstable : (prefixWord ++ tailWord_2972258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972258).length < 2 ^ (prefixWord ++ tailWord_2972258).sum := by decide
  have hdescent : baseEnd_2972258 < baseStart_2972258 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972264 : List Nat := [2, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2]
def baseStart_2972264 : Nat := 118140960795 + 2972264 * 2 ^ 59
def prefixEnd_2972264 : Nat := 4983230072969 + 3 ^ 40 * 2972264 * 2
def baseEnd_2972264 : Nat := 1526200064055264237130813

theorem tailTrace_2972264 : CollatzResearch.WordTrace tailWord_2972264 prefixEnd_2972264 1526200064055264237130813 := by
  unfold tailWord_2972264
  simp only [CollatzResearch.WordTrace]
  refine ⟨54203687052001312561217923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72271582736001750081623897 54203687052001312561217923)
  ·
    refine ⟨81305530578001968841826885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54203687052001312561217923 81305530578001968841826885)
    ·
      refine ⟨15244786983375369157842541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81305530578001968841826885 15244786983375369157842541)
      ·
        refine ⟨5716795118765763434190953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15244786983375369157842541 5716795118765763434190953)
        ·
          refine ⟨4287596339074322575643215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5716795118765763434190953 4287596339074322575643215)
          ·
            refine ⟨6431394508611483863464823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4287596339074322575643215 6431394508611483863464823)
            ·
              refine ⟨9647091762917225795197235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6431394508611483863464823 9647091762917225795197235)
              ·
                refine ⟨14470637644375838692795853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647091762917225795197235 14470637644375838692795853)
                ·
                  refine ⟨5426489116640939509798445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14470637644375838692795853 5426489116640939509798445)
                  ·
                    refine ⟨2034933418740352316174417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5426489116640939509798445 2034933418740352316174417)
                    ·
                      refine ⟨1526200064055264237130813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2034933418740352316174417 1526200064055264237130813)
                      ·
                        rfl

theorem cell23_2972264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 1, 3, 3, 2].length) (baseStart_2972264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972264 prefixEnd_2972264 := by exact prefixLift 2972264
  have htrace : WordTrace (prefixWord ++ tailWord_2972264) baseStart_2972264 baseEnd_2972264 := by
    simpa [prefixWord, tailWord_2972264, baseEnd_2972264] using wordTrace_append hprefix tailTrace_2972264
  have hstable : (prefixWord ++ tailWord_2972264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972264).length < 2 ^ (prefixWord ++ tailWord_2972264).sum := by decide
  have hdescent : baseEnd_2972264 < baseStart_2972264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972273 : List Nat := [1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 4]
def baseStart_2972273 : Nat := 118140960795 + 2972273 * 2 ^ 59
def prefixEnd_2972273 : Nat := 4983230072969 + 3 ^ 40 * 2972273 * 2
def baseEnd_2972273 : Nat := 1526204685381154701918271

theorem tailTrace_2972273 : CollatzResearch.WordTrace tailWord_2972273 prefixEnd_2972273 1526204685381154701918271 := by
  unfold tailWord_2972273
  simp only [CollatzResearch.WordTrace]
  refine ⟨108407702360970019659513473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72271801573980013106342315 108407702360970019659513473)
  ·
    refine ⟨81305776770727514744635105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108407702360970019659513473 81305776770727514744635105)
    ·
      refine ⟨60979332578045636058476329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81305776770727514744635105 60979332578045636058476329)
      ·
        refine ⟨45734499433534227043857247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60979332578045636058476329 45734499433534227043857247)
        ·
          refine ⟨68601749150301340565785871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45734499433534227043857247 68601749150301340565785871)
          ·
            refine ⟨102902623725452010848678807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68601749150301340565785871 102902623725452010848678807)
            ·
              refine ⟨154353935588178016273018211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102902623725452010848678807 154353935588178016273018211)
              ·
                refine ⟨231530903382267024409527317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154353935588178016273018211 231530903382267024409527317)
                ·
                  refine ⟨10853011096043766769196593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 231530903382267024409527317 10853011096043766769196593)
                  ·
                    refine ⟨8139758322032825076897445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10853011096043766769196593 8139758322032825076897445)
                    ·
                      refine ⟨1526204685381154701918271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8139758322032825076897445 1526204685381154701918271)
                      ·
                        rfl

theorem cell23_2972273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_2972273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972273 prefixEnd_2972273 := by exact prefixLift 2972273
  have htrace : WordTrace (prefixWord ++ tailWord_2972273) baseStart_2972273 baseEnd_2972273 := by
    simpa [prefixWord, tailWord_2972273, baseEnd_2972273] using wordTrace_append hprefix tailTrace_2972273
  have hstable : (prefixWord ++ tailWord_2972273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972273).length < 2 ^ (prefixWord ++ tailWord_2972273).sum := by decide
  have hdescent : baseEnd_2972273 < baseStart_2972273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972313 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 1, 7]
def baseStart_2972313 : Nat := 118140960795 + 2972313 * 2 ^ 59
def prefixEnd_2972313 : Nat := 4983230072969 + 3 ^ 40 * 2972313 * 2
def baseEnd_2972313 : Nat := 508741741535778181806029

theorem tailTrace_2972313 : CollatzResearch.WordTrace tailWord_2972313 prefixEnd_2972313 508741741535778181806029 := by
  unfold tailWord_2972313
  simp only [CollatzResearch.WordTrace]
  refine ⟨108409161280825106490969593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72272774187216737660646395 108409161280825106490969593)
  ·
    refine ⟨81306870960618829868227195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108409161280825106490969593 81306870960618829868227195)
    ·
      refine ⟨121960306440928244802340793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81306870960618829868227195 121960306440928244802340793)
      ·
        refine ⟨91470229830696183601755595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121960306440928244802340793 91470229830696183601755595)
        ·
          refine ⟨137205344746044275402633393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91470229830696183601755595 137205344746044275402633393)
          ·
            refine ⟨102904008559533206551975045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137205344746044275402633393 102904008559533206551975045)
            ·
              refine ⟨19294501604912476228495321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 102904008559533206551975045 19294501604912476228495321)
              ·
                refine ⟨14470876203684357171371491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19294501604912476228495321 14470876203684357171371491)
                ·
                  refine ⟨21706314305526535757057237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14470876203684357171371491 21706314305526535757057237)
                  ·
                    refine ⟨508741741535778181806029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21706314305526535757057237 508741741535778181806029)
                    ·
                      rfl

theorem cell23_2972313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 1, 7].length) (baseStart_2972313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972313 prefixEnd_2972313 := by exact prefixLift 2972313
  have htrace : WordTrace (prefixWord ++ tailWord_2972313) baseStart_2972313 baseEnd_2972313 := by
    simpa [prefixWord, tailWord_2972313, baseEnd_2972313] using wordTrace_append hprefix tailTrace_2972313
  have hstable : (prefixWord ++ tailWord_2972313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972313).length < 2 ^ (prefixWord ++ tailWord_2972313).sum := by decide
  have hdescent : baseEnd_2972313 < baseStart_2972313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972323 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5]
def baseStart_2972323 : Nat := 118140960795 + 2972323 * 2 ^ 59
def prefixEnd_2972323 : Nat := 4983230072969 + 3 ^ 40 * 2972323 * 2
def baseEnd_2972323 : Nat := 1526230359413879506293041

theorem tailTrace_2972323 : CollatzResearch.WordTrace tailWord_2972323 prefixEnd_2972323 1526230359413879506293041 := by
  unfold tailWord_2972323
  simp only [CollatzResearch.WordTrace]
  refine ⟨108409526010788878198833623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72273017340525918799222415 108409526010788878198833623)
  ·
    refine ⟨162614289016183317298250435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108409526010788878198833623 162614289016183317298250435)
    ·
      refine ⟨243921433524274975947375653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162614289016183317298250435 243921433524274975947375653)
      ·
        refine ⟨45735268785801557990132935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 243921433524274975947375653 45735268785801557990132935)
        ·
          refine ⟨68602903178702336985199403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45735268785801557990132935 68602903178702336985199403)
          ·
            refine ⟨102904354768053505477799105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68602903178702336985199403 102904354768053505477799105)
            ·
              refine ⟨77178266076040129108349329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102904354768053505477799105 77178266076040129108349329)
              ·
                refine ⟨57883699557030096831261997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77178266076040129108349329 57883699557030096831261997)
                ·
                  refine ⟨21706387333886286311723249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57883699557030096831261997 21706387333886286311723249)
                  ·
                    refine ⟨16279790500414714733792437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21706387333886286311723249 16279790500414714733792437)
                    ·
                      refine ⟨1526230359413879506293041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16279790500414714733792437 1526230359413879506293041)
                      ·
                        rfl

theorem cell23_2972323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 2, 5].length) (baseStart_2972323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972323 prefixEnd_2972323 := by exact prefixLift 2972323
  have htrace : WordTrace (prefixWord ++ tailWord_2972323) baseStart_2972323 baseEnd_2972323 := by
    simpa [prefixWord, tailWord_2972323, baseEnd_2972323] using wordTrace_append hprefix tailTrace_2972323
  have hstable : (prefixWord ++ tailWord_2972323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972323).length < 2 ^ (prefixWord ++ tailWord_2972323).sum := by decide
  have hdescent : baseEnd_2972323 < baseStart_2972323 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972334 : List Nat := [4, 1, 4, 1, 1, 1, 1, 5, 5]
def baseStart_2972334 : Nat := 118140960795 + 2972334 * 2 ^ 59
def prefixEnd_2972334 : Nat := 4983230072969 + 3 ^ 40 * 2972334 * 2
def baseEnd_2972334 : Nat := 169581778633453218139499

theorem tailTrace_2972334 : CollatzResearch.WordTrace tailWord_2972334 prefixEnd_2972334 169581778633453218139499 := by
  unfold tailWord_2972334
  simp only [CollatzResearch.WordTrace]
  refine ⟨13551240901718628384685507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72273284809166018051656037 13551240901718628384685507)
  ·
    refine ⟨20326861352577942577028261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13551240901718628384685507 20326861352577942577028261)
    ·
      refine ⟨3811286503608364233192799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 20326861352577942577028261 3811286503608364233192799)
      ·
        refine ⟨5716929755412546349789199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3811286503608364233192799 5716929755412546349789199)
        ·
          refine ⟨8575394633118819524683799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5716929755412546349789199 8575394633118819524683799)
          ·
            refine ⟨12863091949678229287025699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575394633118819524683799 12863091949678229287025699)
            ·
              refine ⟨19294637924517343930538549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12863091949678229287025699 19294637924517343930538549)
              ·
                refine ⟨1808872305423500993487989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 19294637924517343930538549 1808872305423500993487989)
                ·
                  refine ⟨169581778633453218139499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1808872305423500993487989 169581778633453218139499)
                  ·
                    rfl

theorem cell23_2972334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 5, 5].length) (baseStart_2972334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972334 prefixEnd_2972334 := by exact prefixLift 2972334
  have htrace : WordTrace (prefixWord ++ tailWord_2972334) baseStart_2972334 baseEnd_2972334 := by
    simpa [prefixWord, tailWord_2972334, baseEnd_2972334] using wordTrace_append hprefix tailTrace_2972334
  have hstable : (prefixWord ++ tailWord_2972334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972334).length < 2 ^ (prefixWord ++ tailWord_2972334).sum := by decide
  have hdescent : baseEnd_2972334 < baseStart_2972334 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972387 : List Nat := [1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2972387 : Nat := 118140960795 + 2972387 * 2 ^ 59
def prefixEnd_2972387 : Nat := 4983230072969 + 3 ^ 40 * 2972387 * 2
def baseEnd_2972387 : Nat := 1526263222175767255892747

theorem tailTrace_2972387 : CollatzResearch.WordTrace tailWord_2972387 prefixEnd_2972387 1526263222175767255892747 := by
  unfold tailWord_2972387
  simp only [CollatzResearch.WordTrace]
  refine ⟨108411860282557017129163415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72274573521704678086108943 108411860282557017129163415)
  ·
    refine ⟨162617790423835525693745123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108411860282557017129163415 162617790423835525693745123)
    ·
      refine ⟨243926685635753288540617685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162617790423835525693745123 243926685635753288540617685)
      ·
        refine ⟨5717031694587967700170727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 243926685635753288540617685 5717031694587967700170727)
        ·
          refine ⟨8575547541881951550256091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717031694587967700170727 8575547541881951550256091)
          ·
            refine ⟨12863321312822927325384137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8575547541881951550256091 12863321312822927325384137)
            ·
              refine ⟨9647490984617195494038103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12863321312822927325384137 9647490984617195494038103)
              ·
                refine ⟨14471236476925793241057155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647490984617195494038103 14471236476925793241057155)
                ·
                  refine ⟨21706854715388689861585733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14471236476925793241057155 21706854715388689861585733)
                  ·
                    refine ⟨4070035259135379349047325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21706854715388689861585733 4070035259135379349047325)
                    ·
                      refine ⟨1526263222175767255892747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070035259135379349047325 1526263222175767255892747)
                      ·
                        rfl

theorem cell23_2972387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2972387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972387 prefixEnd_2972387 := by exact prefixLift 2972387
  have htrace : WordTrace (prefixWord ++ tailWord_2972387) baseStart_2972387 baseEnd_2972387 := by
    simpa [prefixWord, tailWord_2972387, baseEnd_2972387] using wordTrace_append hprefix tailTrace_2972387
  have hstable : (prefixWord ++ tailWord_2972387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972387).length < 2 ^ (prefixWord ++ tailWord_2972387).sum := by decide
  have hdescent : baseEnd_2972387 < baseStart_2972387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972424 : List Nat := [2, 1, 3, 2, 2, 4, 2, 1, 6]
def baseStart_2972424 : Nat := 118140960795 + 2972424 * 2 ^ 59
def prefixEnd_2972424 : Nat := 4983230072969 + 3 ^ 40 * 2972424 * 2
def baseEnd_2972424 : Nat := 169586913439998179014453

theorem tailTrace_2972424 : CollatzResearch.WordTrace tailWord_2972424 prefixEnd_2972424 169586913439998179014453 := by
  unfold tailWord_2972424
  simp only [CollatzResearch.WordTrace]
  refine ⟨54206604891711486224130163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72275473188948648298840217 54206604891711486224130163)
  ·
    refine ⟨81309907337567229336195245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54206604891711486224130163 81309907337567229336195245)
    ·
      refine ⟨30491215251587711001073217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81309907337567229336195245 30491215251587711001073217)
      ·
        refine ⟨22868411438690783250804913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30491215251587711001073217 22868411438690783250804913)
        ·
          refine ⟨17151308579018087438103685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22868411438690783250804913 17151308579018087438103685)
          ·
            refine ⟨3215870358565891394644441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17151308579018087438103685 3215870358565891394644441)
            ·
              refine ⟨2411902768924418545983331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215870358565891394644441 2411902768924418545983331)
              ·
                refine ⟨3617854153386627818974997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411902768924418545983331 3617854153386627818974997)
                ·
                  refine ⟨169586913439998179014453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3617854153386627818974997 169586913439998179014453)
                  ·
                    rfl

theorem cell23_2972424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 4, 2, 1, 6].length) (baseStart_2972424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972424 prefixEnd_2972424 := by exact prefixLift 2972424
  have htrace : WordTrace (prefixWord ++ tailWord_2972424) baseStart_2972424 baseEnd_2972424 := by
    simpa [prefixWord, tailWord_2972424, baseEnd_2972424] using wordTrace_append hprefix tailTrace_2972424
  have hstable : (prefixWord ++ tailWord_2972424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972424).length < 2 ^ (prefixWord ++ tailWord_2972424).sum := by decide
  have hdescent : baseEnd_2972424 < baseStart_2972424 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972427 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 6, 3, 2]
def baseStart_2972427 : Nat := 118140960795 + 2972427 * 2 ^ 59
def prefixEnd_2972427 : Nat := 4983230072969 + 3 ^ 40 * 2972427 * 2
def baseEnd_2972427 : Nat := 1526283761401947099392563

theorem tailTrace_2972427 : CollatzResearch.WordTrace tailWord_2972427 prefixEnd_2972427 1526283761401947099392563 := by
  unfold tailWord_2972427
  simp only [CollatzResearch.WordTrace]
  refine ⟨108413319202412103960619535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72275546134941402640413023 108413319202412103960619535)
  ·
    refine ⟨162619978803618155940929303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108413319202412103960619535 162619978803618155940929303)
    ·
      refine ⟨243929968205427233911393955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162619978803618155940929303 243929968205427233911393955)
      ·
        refine ⟨365894952308140850867090933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243929968205427233911393955 365894952308140850867090933)
        ·
          refine ⟨34302651778888204768789775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 365894952308140850867090933 34302651778888204768789775)
          ·
            refine ⟨51453977668332307153184663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34302651778888204768789775 51453977668332307153184663)
            ·
              refine ⟨77180966502498460729776995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51453977668332307153184663 77180966502498460729776995)
              ·
                refine ⟨115771449753747691094665493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 77180966502498460729776995 115771449753747691094665493)
                ·
                  refine ⟨5426786707206923020062445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 115771449753747691094665493 5426786707206923020062445)
                  ·
                    refine ⟨2035045015202596132523417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5426786707206923020062445 2035045015202596132523417)
                    ·
                      refine ⟨1526283761401947099392563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035045015202596132523417 1526283761401947099392563)
                      ·
                        rfl

theorem cell23_2972427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 6, 3, 2].length) (baseStart_2972427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972427 prefixEnd_2972427 := by exact prefixLift 2972427
  have htrace : WordTrace (prefixWord ++ tailWord_2972427) baseStart_2972427 baseEnd_2972427 := by
    simpa [prefixWord, tailWord_2972427, baseEnd_2972427] using wordTrace_append hprefix tailTrace_2972427
  have hstable : (prefixWord ++ tailWord_2972427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972427).length < 2 ^ (prefixWord ++ tailWord_2972427).sum := by decide
  have hdescent : baseEnd_2972427 < baseStart_2972427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972444 : List Nat := [2, 2, 3, 1, 1, 3, 1, 3, 2, 3, 2]
def baseStart_2972444 : Nat := 118140960795 + 2972444 * 2 ^ 59
def prefixEnd_2972444 : Nat := 4983230072969 + 3 ^ 40 * 2972444 * 2
def baseEnd_2972444 : Nat := 1526292490573073532879985

theorem tailTrace_2972444 : CollatzResearch.WordTrace tailWord_2972444 prefixEnd_2972444 1526292490573073532879985 := by
  unfold tailWord_2972444
  simp only [CollatzResearch.WordTrace]
  refine ⟨54206969621675257931994193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72275959495567010575992257 54206969621675257931994193)
  ·
    refine ⟨40655227216256443448995645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54206969621675257931994193 40655227216256443448995645)
    ·
      refine ⟨15245710206096166293373367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40655227216256443448995645 15245710206096166293373367)
      ·
        refine ⟨22868565309144249440060051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15245710206096166293373367 22868565309144249440060051)
        ·
          refine ⟨34302847963716374160090077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22868565309144249440060051 34302847963716374160090077)
          ·
            refine ⟨12863567986393640310033779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34302847963716374160090077 12863567986393640310033779)
            ·
              refine ⟨19295351979590460465050669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12863567986393640310033779 19295351979590460465050669)
              ·
                refine ⟨7235756992346422674394001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19295351979590460465050669 7235756992346422674394001)
                ·
                  refine ⟨5426817744259817005795501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7235756992346422674394001 5426817744259817005795501)
                  ·
                    refine ⟨2035056654097431377173313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5426817744259817005795501 2035056654097431377173313)
                    ·
                      refine ⟨1526292490573073532879985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035056654097431377173313 1526292490573073532879985)
                      ·
                        rfl

theorem cell23_2972444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 3, 2, 3, 2].length) (baseStart_2972444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972444 prefixEnd_2972444 := by exact prefixLift 2972444
  have htrace : WordTrace (prefixWord ++ tailWord_2972444) baseStart_2972444 baseEnd_2972444 := by
    simpa [prefixWord, tailWord_2972444, baseEnd_2972444] using wordTrace_append hprefix tailTrace_2972444
  have hstable : (prefixWord ++ tailWord_2972444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972444).length < 2 ^ (prefixWord ++ tailWord_2972444).sum := by decide
  have hdescent : baseEnd_2972444 < baseStart_2972444 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972508 : List Nat := [2, 2, 4, 2, 1, 3, 2, 1, 1, 1, 4]
def baseStart_2972508 : Nat := 118140960795 + 2972508 * 2 ^ 59
def prefixEnd_2972508 : Nat := 4983230072969 + 3 ^ 40 * 2972508 * 2
def baseEnd_2972508 : Nat := 1526325353334961282479691

theorem tailTrace_2972508 : CollatzResearch.WordTrace tailWord_2972508 prefixEnd_2972508 1526325353334961282479691 := by
  unfold tailWord_2972508
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208136757559327397159089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72277515676745769862878785 54208136757559327397159089)
  ·
    refine ⟨40656102568169495547869317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54208136757559327397159089 40656102568169495547869317)
    ·
      refine ⟨7623019231531780415225497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40656102568169495547869317 7623019231531780415225497)
      ·
        refine ⟨5717264423648835311419123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7623019231531780415225497 5717264423648835311419123)
        ·
          refine ⟨8575896635473252967128685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717264423648835311419123 8575896635473252967128685)
          ·
            refine ⟨3215961238302469862673257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8575896635473252967128685 3215961238302469862673257)
            ·
              refine ⟨2411970928726852397004943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3215961238302469862673257 2411970928726852397004943)
              ·
                refine ⟨3617956393090278595507415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2411970928726852397004943 3617956393090278595507415)
                ·
                  refine ⟨5426934589635417893261123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3617956393090278595507415 5426934589635417893261123)
                  ·
                    refine ⟨8140401884453126839891685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5426934589635417893261123 8140401884453126839891685)
                    ·
                      refine ⟨1526325353334961282479691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8140401884453126839891685 1526325353334961282479691)
                      ·
                        rfl

theorem cell23_2972508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 2, 1, 1, 1, 4].length) (baseStart_2972508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972508 prefixEnd_2972508 := by exact prefixLift 2972508
  have htrace : WordTrace (prefixWord ++ tailWord_2972508) baseStart_2972508 baseEnd_2972508 := by
    simpa [prefixWord, tailWord_2972508, baseEnd_2972508] using wordTrace_append hprefix tailTrace_2972508
  have hstable : (prefixWord ++ tailWord_2972508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972508).length < 2 ^ (prefixWord ++ tailWord_2972508).sum := by decide
  have hdescent : baseEnd_2972508 < baseStart_2972508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972524 : List Nat := [2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 3]
def baseStart_2972524 : Nat := 118140960795 + 2972524 * 2 ^ 59
def prefixEnd_2972524 : Nat := 4983230072969 + 3 ^ 40 * 2972524 * 2
def baseEnd_2972524 : Nat := 1526333569025433219879617

theorem tailTrace_2972524 : CollatzResearch.WordTrace tailWord_2972524 prefixEnd_2972524 1526333569025433219879617 := by
  unfold tailWord_2972524
  simp only [CollatzResearch.WordTrace]
  refine ⟨54208428541530344763450313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72277904722040459684600417 54208428541530344763450313)
  ·
    refine ⟨40656321406147758572587735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54208428541530344763450313 40656321406147758572587735)
    ·
      refine ⟨60984482109221637858881603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40656321406147758572587735 60984482109221637858881603)
      ·
        refine ⟨91476723163832456788322405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60984482109221637858881603 91476723163832456788322405)
        ·
          refine ⟨17151885593218585647810451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91476723163832456788322405 17151885593218585647810451)
          ·
            refine ⟨25727828389827878471715677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17151885593218585647810451 25727828389827878471715677)
            ·
              refine ⟨9647935646185454426893379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25727828389827878471715677 9647935646185454426893379)
              ·
                refine ⟨14471903469278181640340069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9647935646185454426893379 14471903469278181640340069)
                ·
                  refine ⟨2713481900489659057563763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14471903469278181640340069 2713481900489659057563763)
                  ·
                    refine ⟨4070222850734488586345645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713481900489659057563763 4070222850734488586345645)
                    ·
                      refine ⟨1526333569025433219879617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070222850734488586345645 1526333569025433219879617)
                      ·
                        rfl

theorem cell23_2972524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 3].length) (baseStart_2972524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972524 prefixEnd_2972524 := by exact prefixLift 2972524
  have htrace : WordTrace (prefixWord ++ tailWord_2972524) baseStart_2972524 baseEnd_2972524 := by
    simpa [prefixWord, tailWord_2972524, baseEnd_2972524] using wordTrace_append hprefix tailTrace_2972524
  have hstable : (prefixWord ++ tailWord_2972524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972524).length < 2 ^ (prefixWord ++ tailWord_2972524).sum := by decide
  have hdescent : baseEnd_2972524 < baseStart_2972524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972551 : List Nat := [1, 1, 4, 2, 3, 1, 1, 4, 1, 3, 2]
def baseStart_2972551 : Nat := 118140960795 + 2972551 * 2 ^ 59
def prefixEnd_2972551 : Nat := 4983230072969 + 3 ^ 40 * 2972551 * 2
def baseEnd_2972551 : Nat := 1526347433003104614241993

theorem tailTrace_2972551 : CollatzResearch.WordTrace tailWord_2972551 prefixEnd_2972551 1526347433003104614241993 := by
  unfold tailWord_2972551
  simp only [CollatzResearch.WordTrace]
  refine ⟨108417841853962873138133507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72278561235975248758755671 108417841853962873138133507)
  ·
    refine ⟨162626762780944309707200261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108417841853962873138133507 162626762780944309707200261)
    ·
      refine ⟨30492518021427058070100049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162626762780944309707200261 30492518021427058070100049)
      ·
        refine ⟨22869388516070293552575037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30492518021427058070100049 22869388516070293552575037)
        ·
          refine ⟨8576020693526360082215639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22869388516070293552575037 8576020693526360082215639)
          ·
            refine ⟨12864031040289540123323459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576020693526360082215639 12864031040289540123323459)
            ·
              refine ⟨19296046560434310184985189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12864031040289540123323459 19296046560434310184985189)
              ·
                refine ⟨3618008730081433159684723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19296046560434310184985189 3618008730081433159684723)
                ·
                  refine ⟨5427013095122149739527085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618008730081433159684723 5427013095122149739527085)
                  ·
                    refine ⟨2035129910670806152322657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5427013095122149739527085 2035129910670806152322657)
                    ·
                      refine ⟨1526347433003104614241993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035129910670806152322657 1526347433003104614241993)
                      ·
                        rfl

theorem cell23_2972551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 1, 4, 1, 3, 2].length) (baseStart_2972551 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972551 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972551 prefixEnd_2972551 := by exact prefixLift 2972551
  have htrace : WordTrace (prefixWord ++ tailWord_2972551) baseStart_2972551 baseEnd_2972551 := by
    simpa [prefixWord, tailWord_2972551, baseEnd_2972551] using wordTrace_append hprefix tailTrace_2972551
  have hstable : (prefixWord ++ tailWord_2972551).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972551).length < 2 ^ (prefixWord ++ tailWord_2972551).sum := by decide
  have hdescent : baseEnd_2972551 < baseStart_2972551 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972560 : List Nat := [2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6]
def baseStart_2972560 : Nat := 118140960795 + 2972560 * 2 ^ 59
def prefixEnd_2972560 : Nat := 4983230072969 + 3 ^ 40 * 2972560 * 2
def baseEnd_2972560 : Nat := 1526352054328995079029451

theorem tailTrace_2972560 : CollatzResearch.WordTrace tailWord_2972560 prefixEnd_2972560 1526352054328995079029451 := by
  unfold tailWord_2972560
  simp only [CollatzResearch.WordTrace]
  refine ⟨54209085055465133837605567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72278780073953511783474089 54209085055465133837605567)
  ·
    refine ⟨81313627583197700756408351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54209085055465133837605567 81313627583197700756408351)
    ·
      refine ⟨121970441374796551134612527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81313627583197700756408351 121970441374796551134612527)
      ·
        refine ⟨182955662062194826701918791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121970441374796551134612527 182955662062194826701918791)
        ·
          refine ⟨274433493093292240052878187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182955662062194826701918791 274433493093292240052878187)
          ·
            refine ⟨411650239639938360079317281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274433493093292240052878187 411650239639938360079317281)
            ·
              refine ⟨308737679729953770059487961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 411650239639938360079317281 308737679729953770059487961)
              ·
                refine ⟨231553259797465327544615971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 308737679729953770059487961 231553259797465327544615971)
                ·
                  refine ⟨347329889696197991316923957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 231553259797465327544615971 347329889696197991316923957)
                  ·
                    refine ⟨32562177159018561685961621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 347329889696197991316923957 32562177159018561685961621)
                    ·
                      refine ⟨1526352054328995079029451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32562177159018561685961621 1526352054328995079029451)
                      ·
                        rfl

theorem cell23_2972560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 6].length) (baseStart_2972560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972560 prefixEnd_2972560 := by exact prefixLift 2972560
  have htrace : WordTrace (prefixWord ++ tailWord_2972560) baseStart_2972560 baseEnd_2972560 := by
    simpa [prefixWord, tailWord_2972560, baseEnd_2972560] using wordTrace_append hprefix tailTrace_2972560
  have hstable : (prefixWord ++ tailWord_2972560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972560).length < 2 ^ (prefixWord ++ tailWord_2972560).sum := by decide
  have hdescent : baseEnd_2972560 < baseStart_2972560 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972567 : List Nat := [1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5]
def baseStart_2972567 : Nat := 118140960795 + 2972567 * 2 ^ 59
def prefixEnd_2972567 : Nat := 4983230072969 + 3 ^ 40 * 2972567 * 2
def baseEnd_2972567 : Nat := 1526355648693576551641919

theorem tailTrace_2972567 : CollatzResearch.WordTrace tailWord_2972567 prefixEnd_2972567 1526355648693576551641919 := by
  unfold tailWord_2972567
  simp only [CollatzResearch.WordTrace]
  refine ⟨108418425421904907870715955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72278950281269938580477303 108418425421904907870715955)
  ·
    refine ⟨162627638132857361806073933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108418425421904907870715955 162627638132857361806073933)
    ·
      refine ⟨60985364299821510677277725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162627638132857361806073933 60985364299821510677277725)
      ·
        refine ⟨22869511612433066503979147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60985364299821510677277725 22869511612433066503979147)
        ·
          refine ⟨34304267418649599755968721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22869511612433066503979147 34304267418649599755968721)
          ·
            refine ⟨25728200563987199816976541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34304267418649599755968721 25728200563987199816976541)
            ·
              refine ⟨9648075211495199931366203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25728200563987199816976541 9648075211495199931366203)
              ·
                refine ⟨14472112817242799897049305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9648075211495199931366203 14472112817242799897049305)
                ·
                  refine ⟨10854084612932099922786979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14472112817242799897049305 10854084612932099922786979)
                  ·
                    refine ⟨16281126919398149884180469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10854084612932099922786979 16281126919398149884180469)
                    ·
                      refine ⟨1526355648693576551641919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16281126919398149884180469 1526355648693576551641919)
                      ·
                        rfl

theorem cell23_2972567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_2972567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972567 prefixEnd_2972567 := by exact prefixLift 2972567
  have htrace : WordTrace (prefixWord ++ tailWord_2972567) baseStart_2972567 baseEnd_2972567 := by
    simpa [prefixWord, tailWord_2972567, baseEnd_2972567] using wordTrace_append hprefix tailTrace_2972567
  have hstable : (prefixWord ++ tailWord_2972567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972567).length < 2 ^ (prefixWord ++ tailWord_2972567).sum := by decide
  have hdescent : baseEnd_2972567 < baseStart_2972567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972634 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 2, 5]
def baseStart_2972634 : Nat := 118140960795 + 2972634 * 2 ^ 59
def prefixEnd_2972634 : Nat := 4983230072969 + 3 ^ 40 * 2972634 * 2
def baseEnd_2972634 : Nat := 508796683965809263168037

theorem tailTrace_2972634 : CollatzResearch.WordTrace tailWord_2972634 prefixEnd_2972634 508796683965809263168037 := by
  unfold tailWord_2972634
  simp only [CollatzResearch.WordTrace]
  refine ⟨27105217278165544578351239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72280579408441452208936637 27105217278165544578351239)
  ·
    refine ⟨40657825917248316867526859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27105217278165544578351239 40657825917248316867526859)
    ·
      refine ⟨60986738875872475301290289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40657825917248316867526859 60986738875872475301290289)
      ·
        refine ⟨45740054156904356475967717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60986738875872475301290289 45740054156904356475967717)
        ·
          refine ⟨8576260154419566839243947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45740054156904356475967717 8576260154419566839243947)
          ·
            refine ⟨12864390231629350258865921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576260154419566839243947 12864390231629350258865921)
            ·
              refine ⟨9648292673722012694149441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12864390231629350258865921 9648292673722012694149441)
              ·
                refine ⟨7236219505291509520612081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9648292673722012694149441 7236219505291509520612081)
                ·
                  refine ⟨5427164628968632140459061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7236219505291509520612081 5427164628968632140459061)
                  ·
                    refine ⟨508796683965809263168037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5427164628968632140459061 508796683965809263168037)
                    ·
                      rfl

theorem cell23_2972634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 2, 5].length) (baseStart_2972634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972634 prefixEnd_2972634 := by exact prefixLift 2972634
  have htrace : WordTrace (prefixWord ++ tailWord_2972634) baseStart_2972634 baseEnd_2972634 := by
    simpa [prefixWord, tailWord_2972634, baseEnd_2972634] using wordTrace_append hprefix tailTrace_2972634
  have hstable : (prefixWord ++ tailWord_2972634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972634).length < 2 ^ (prefixWord ++ tailWord_2972634).sum := by decide
  have hdescent : baseEnd_2972634 < baseStart_2972634 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972677 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 8]
def baseStart_2972677 : Nat := 118140960795 + 2972677 * 2 ^ 59
def prefixEnd_2972677 : Nat := 4983230072969 + 3 ^ 40 * 2972677 * 2
def baseEnd_2972677 : Nat := 169601347951730124585157

theorem tailTrace_2972677 : CollatzResearch.WordTrace tailWord_2972677 prefixEnd_2972677 169601347951730124585157 := by
  unfold tailWord_2972677
  simp only [CollatzResearch.WordTrace]
  refine ⟨108422437451506396657220285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72281624967670931104813523 108422437451506396657220285)
  ·
    refine ⟨40658414044314898746457607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108422437451506396657220285 40658414044314898746457607)
    ·
      refine ⟨60987621066472348119686411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40658414044314898746457607 60987621066472348119686411)
      ·
        refine ⟨91481431599708522179529617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60987621066472348119686411 91481431599708522179529617)
        ·
          refine ⟨68611073699781391634647213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91481431599708522179529617 68611073699781391634647213)
          ·
            refine ⟨25729152637418021862992705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68611073699781391634647213 25729152637418021862992705)
            ·
              refine ⟨19296864478063516397244529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25729152637418021862992705 19296864478063516397244529)
              ·
                refine ⟨14472648358547637297933397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19296864478063516397244529 14472648358547637297933397)
                ·
                  refine ⟨169601347951730124585157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 14472648358547637297933397 169601347951730124585157)
                  ·
                    rfl

theorem cell23_2972677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_2972677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972677 prefixEnd_2972677 := by exact prefixLift 2972677
  have htrace : WordTrace (prefixWord ++ tailWord_2972677) baseStart_2972677 baseEnd_2972677 := by
    simpa [prefixWord, tailWord_2972677, baseEnd_2972677] using wordTrace_append hprefix tailTrace_2972677
  have hstable : (prefixWord ++ tailWord_2972677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972677).length < 2 ^ (prefixWord ++ tailWord_2972677).sum := by decide
  have hdescent : baseEnd_2972677 < baseStart_2972677 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972697 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 6]
def baseStart_2972697 : Nat := 118140960795 + 2972697 * 2 ^ 59
def prefixEnd_2972697 : Nat := 4983230072969 + 3 ^ 40 * 2972697 * 2
def baseEnd_2972697 : Nat := 1526422401178661043016321

theorem tailTrace_2972697 : CollatzResearch.WordTrace tailWord_2972697 prefixEnd_2972697 1526422401178661043016321 := by
  unfold tailWord_2972697
  simp only [CollatzResearch.WordTrace]
  refine ⟨108423166911433940072948345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72282111274289293381965563 108423166911433940072948345)
  ·
    refine ⟨81317375183575455054711259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108423166911433940072948345 81317375183575455054711259)
    ·
      refine ⟨121976062775363182582066889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81317375183575455054711259 121976062775363182582066889)
      ·
        refine ⟨91482047081522386936550167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121976062775363182582066889 91482047081522386936550167)
        ·
          refine ⟨137223070622283580404825251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91482047081522386936550167 137223070622283580404825251)
          ·
            refine ⟨205834605933425370607237877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137223070622283580404825251 205834605933425370607237877)
            ·
              refine ⟨19296994306258628494428551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 205834605933425370607237877 19296994306258628494428551)
              ·
                refine ⟨28945491459387942741642827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19296994306258628494428551 28945491459387942741642827)
                ·
                  refine ⟨43418237189081914112464241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28945491459387942741642827 43418237189081914112464241)
                  ·
                    refine ⟨32563677891811435584348181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 43418237189081914112464241 32563677891811435584348181)
                    ·
                      refine ⟨1526422401178661043016321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32563677891811435584348181 1526422401178661043016321)
                      ·
                        rfl

theorem cell23_2972697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 2, 6].length) (baseStart_2972697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972697 prefixEnd_2972697 := by exact prefixLift 2972697
  have htrace : WordTrace (prefixWord ++ tailWord_2972697) baseStart_2972697 baseEnd_2972697 := by
    simpa [prefixWord, tailWord_2972697, baseEnd_2972697] using wordTrace_append hprefix tailTrace_2972697
  have hstable : (prefixWord ++ tailWord_2972697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972697).length < 2 ^ (prefixWord ++ tailWord_2972697).sum := by decide
  have hdescent : baseEnd_2972697 < baseStart_2972697 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972721 : List Nat := [1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 3]
def baseStart_2972721 : Nat := 118140960795 + 2972721 * 2 ^ 59
def prefixEnd_2972721 : Nat := 4983230072969 + 3 ^ 40 * 2972721 * 2
def baseEnd_2972721 : Nat := 1526434724714368949116211

theorem tailTrace_2972721 : CollatzResearch.WordTrace tailWord_2972721 prefixEnd_2972721 1526434724714368949116211 := by
  unfold tailWord_2972721
  simp only [CollatzResearch.WordTrace]
  refine ⟨108424042263346992171822017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72282694842231328114548011 108424042263346992171822017)
  ·
    refine ⟨81318031697510244128866513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108424042263346992171822017 81318031697510244128866513)
    ·
      refine ⟨60988523773132683096649885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81318031697510244128866513 60988523773132683096649885)
      ·
        refine ⟨22870696414924756161243707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60988523773132683096649885 22870696414924756161243707)
        ·
          refine ⟨34306044622387134241865561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22870696414924756161243707 34306044622387134241865561)
          ·
            refine ⟨25729533466790350681399171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34306044622387134241865561 25729533466790350681399171)
            ·
              refine ⟨38594300200185526022098757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25729533466790350681399171 38594300200185526022098757)
              ·
                refine ⟨7236431287534786129143517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38594300200185526022098757 7236431287534786129143517)
                ·
                  refine ⟨2713661732825544798428819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7236431287534786129143517 2713661732825544798428819)
                  ·
                    refine ⟨4070492599238317197643229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713661732825544798428819 4070492599238317197643229)
                    ·
                      refine ⟨1526434724714368949116211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070492599238317197643229 1526434724714368949116211)
                      ·
                        rfl

theorem cell23_2972721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 1, 4, 3, 1, 3].length) (baseStart_2972721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972721 prefixEnd_2972721 := by exact prefixLift 2972721
  have htrace : WordTrace (prefixWord ++ tailWord_2972721) baseStart_2972721 baseEnd_2972721 := by
    simpa [prefixWord, tailWord_2972721, baseEnd_2972721] using wordTrace_append hprefix tailTrace_2972721
  have hstable : (prefixWord ++ tailWord_2972721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972721).length < 2 ^ (prefixWord ++ tailWord_2972721).sum := by decide
  have hdescent : baseEnd_2972721 < baseStart_2972721 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972778 : List Nat := [3, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_2972778 : Nat := 118140960795 + 2972778 * 2 ^ 59
def prefixEnd_2972778 : Nat := 4983230072969 + 3 ^ 40 * 2972778 * 2
def baseEnd_2972778 : Nat := 1526463993111675226103449

theorem tailTrace_2972778 : CollatzResearch.WordTrace tailWord_2972778 prefixEnd_2972778 1526463993111675226103449 := by
  unfold tailWord_2972778
  simp only [CollatzResearch.WordTrace]
  refine ⟨27106530306035122726661747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72284080816093660604431325 27106530306035122726661747)
  ·
    refine ⟨40659795459052684089992621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27106530306035122726661747 40659795459052684089992621)
    ·
      refine ⟨15247423297144756533747233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40659795459052684089992621 15247423297144756533747233)
      ·
        refine ⟨11435567472858567400310425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15247423297144756533747233 11435567472858567400310425)
        ·
          refine ⟨8576675604643925550232819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11435567472858567400310425 8576675604643925550232819)
          ·
            refine ⟨12865013406965888325349229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576675604643925550232819 12865013406965888325349229)
            ·
              refine ⟨4824380027612208122005961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12865013406965888325349229 4824380027612208122005961)
              ·
                refine ⟨3618285020709156091504471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824380027612208122005961 3618285020709156091504471)
                ·
                  refine ⟨5427427531063734137256707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3618285020709156091504471 5427427531063734137256707)
                  ·
                    refine ⟨8141141296595601205885061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5427427531063734137256707 8141141296595601205885061)
                    ·
                      refine ⟨1526463993111675226103449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8141141296595601205885061 1526463993111675226103449)
                      ·
                        rfl

theorem cell23_2972778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_2972778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972778 prefixEnd_2972778 := by exact prefixLift 2972778
  have htrace : WordTrace (prefixWord ++ tailWord_2972778) baseStart_2972778 baseEnd_2972778 := by
    simpa [prefixWord, tailWord_2972778, baseEnd_2972778] using wordTrace_append hprefix tailTrace_2972778
  have hstable : (prefixWord ++ tailWord_2972778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972778).length < 2 ^ (prefixWord ++ tailWord_2972778).sum := by decide
  have hdescent : baseEnd_2972778 < baseStart_2972778 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972811 : List Nat := [1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 3]
def baseStart_2972811 : Nat := 118140960795 + 2972811 * 2 ^ 59
def prefixEnd_2972811 : Nat := 4983230072969 + 3 ^ 40 * 2972811 * 2
def baseEnd_2972811 : Nat := 1526480937973273596990797

theorem tailTrace_2972811 : CollatzResearch.WordTrace tailWord_2972811 prefixEnd_2972811 1526480937973273596990797 := by
  unfold tailWord_2972811
  simp only [CollatzResearch.WordTrace]
  refine ⟨108427324833020937542598287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72284883222013958361732191 108427324833020937542598287)
  ·
    refine ⟨162640987249531406313897431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108427324833020937542598287 162640987249531406313897431)
    ·
      refine ⟨243961480874297109470846147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162640987249531406313897431 243961480874297109470846147)
      ·
        refine ⟨365942221311445664206269221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 243961480874297109470846147 365942221311445664206269221)
        ·
          refine ⟨68614166495896062038675479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 365942221311445664206269221 68614166495896062038675479)
          ·
            refine ⟨102921249743844093058013219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68614166495896062038675479 102921249743844093058013219)
            ·
              refine ⟨154381874615766139587019829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102921249743844093058013219 154381874615766139587019829)
              ·
                refine ⟨14473300745228075586283109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154381874615766139587019829 14473300745228075586283109)
                ·
                  refine ⟨2713743889730264172428083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14473300745228075586283109 2713743889730264172428083)
                  ·
                    refine ⟨4070615834595396258642125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713743889730264172428083 4070615834595396258642125)
                    ·
                      refine ⟨1526480937973273596990797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070615834595396258642125 1526480937973273596990797)
                      ·
                        rfl

theorem cell23_2972811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 5, 4, 1, 3].length) (baseStart_2972811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972811 prefixEnd_2972811 := by exact prefixLift 2972811
  have htrace : WordTrace (prefixWord ++ tailWord_2972811) baseStart_2972811 baseEnd_2972811 := by
    simpa [prefixWord, tailWord_2972811, baseEnd_2972811] using wordTrace_append hprefix tailTrace_2972811
  have hstable : (prefixWord ++ tailWord_2972811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972811).length < 2 ^ (prefixWord ++ tailWord_2972811).sum := by decide
  have hdescent : baseEnd_2972811 < baseStart_2972811 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972828 : List Nat := [2, 2, 3, 2, 1, 3, 2, 1, 1, 3, 3]
def baseStart_2972828 : Nat := 118140960795 + 2972828 * 2 ^ 59
def prefixEnd_2972828 : Nat := 4983230072969 + 3 ^ 40 * 2972828 * 2
def baseEnd_2972828 : Nat := 1526489667144400030478219

theorem tailTrace_2972828 : CollatzResearch.WordTrace tailWord_2972828 prefixEnd_2972828 1526489667144400030478219 := by
  unfold tailWord_2972828
  simp only [CollatzResearch.WordTrace]
  refine ⟨54213972436979674722983569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72285296582639566297311425 54213972436979674722983569)
  ·
    refine ⟨40660479327734756042237677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54213972436979674722983569 40660479327734756042237677)
    ·
      refine ⟨15247679747900533515839129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40660479327734756042237677 15247679747900533515839129)
      ·
        refine ⟨11435759810925400136879347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15247679747900533515839129 11435759810925400136879347)
        ·
          refine ⟨17153639716388100205319021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11435759810925400136879347 17153639716388100205319021)
          ·
            refine ⟨6432614893645537576994633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17153639716388100205319021 6432614893645537576994633)
            ·
              refine ⟨4824461170234153182745975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6432614893645537576994633 4824461170234153182745975)
              ·
                refine ⟨7236691755351229774118963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824461170234153182745975 7236691755351229774118963)
                ·
                  refine ⟨10855037633026844661178445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7236691755351229774118963 10855037633026844661178445)
                  ·
                    refine ⟨4070639112385066747941917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10855037633026844661178445 4070639112385066747941917)
                    ·
                      refine ⟨1526489667144400030478219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070639112385066747941917 1526489667144400030478219)
                      ·
                        rfl

theorem cell23_2972828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 1, 1, 3, 3].length) (baseStart_2972828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972828 prefixEnd_2972828 := by exact prefixLift 2972828
  have htrace : WordTrace (prefixWord ++ tailWord_2972828) baseStart_2972828 baseEnd_2972828 := by
    simpa [prefixWord, tailWord_2972828, baseEnd_2972828] using wordTrace_append hprefix tailTrace_2972828
  have hstable : (prefixWord ++ tailWord_2972828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972828).length < 2 ^ (prefixWord ++ tailWord_2972828).sum := by decide
  have hdescent : baseEnd_2972828 < baseStart_2972828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972862 : List Nat := [4, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3]
def baseStart_2972862 : Nat := 118140960795 + 2972862 * 2 ^ 59
def prefixEnd_2972862 : Nat := 4983230072969 + 3 ^ 40 * 2972862 * 2
def baseEnd_2972862 : Nat := 1526507125486652897453063

theorem tailTrace_2972862 : CollatzResearch.WordTrace tailWord_2972862 prefixEnd_2972862 1526507125486652897453063 := by
  unfold tailWord_2972862
  simp only [CollatzResearch.WordTrace]
  refine ⟨13553648119479521656588105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72286123303890782168469893 13553648119479521656588105)
  ·
    refine ⟨10165236089609641242441079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13553648119479521656588105 10165236089609641242441079)
    ·
      refine ⟨15247854134414461863661619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10165236089609641242441079 15247854134414461863661619)
      ·
        refine ⟨22871781201621692795492429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15247854134414461863661619 22871781201621692795492429)
        ·
          refine ⟨8576917950608134798309661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22871781201621692795492429 8576917950608134798309661)
          ·
            refine ⟨3216344231478050549366123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8576917950608134798309661 3216344231478050549366123)
            ·
              refine ⟨4824516347217075824049185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216344231478050549366123 4824516347217075824049185)
              ·
                refine ⟨3618387260412806868036889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824516347217075824049185 3618387260412806868036889)
                ·
                  refine ⟨2713790445309605151027667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618387260412806868036889 2713790445309605151027667)
                  ·
                    refine ⟨4070685667964407726541501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713790445309605151027667 4070685667964407726541501)
                    ·
                      refine ⟨1526507125486652897453063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070685667964407726541501 1526507125486652897453063)
                      ·
                        rfl

theorem cell23_2972862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 2, 2, 1, 3].length) (baseStart_2972862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972862 prefixEnd_2972862 := by exact prefixLift 2972862
  have htrace : WordTrace (prefixWord ++ tailWord_2972862) baseStart_2972862 baseEnd_2972862 := by
    simpa [prefixWord, tailWord_2972862, baseEnd_2972862] using wordTrace_append hprefix tailTrace_2972862
  have hstable : (prefixWord ++ tailWord_2972862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972862).length < 2 ^ (prefixWord ++ tailWord_2972862).sum := by decide
  have hdescent : baseEnd_2972862 < baseStart_2972862 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972885 : List Nat := [1, 3, 2, 4, 1, 1, 3, 1, 1, 4, 2]
def baseStart_2972885 : Nat := 118140960795 + 2972885 * 2 ^ 59
def prefixEnd_2972885 : Nat := 4983230072969 + 3 ^ 40 * 2972885 * 2
def baseEnd_2972885 : Nat := 1526518935541706307465457

theorem tailTrace_2972885 : CollatzResearch.WordTrace tailWord_2972885 prefixEnd_2972885 1526518935541706307465457 := by
  unfold tailWord_2972885
  simp only [CollatzResearch.WordTrace]
  refine ⟨108430023834752848180792109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72286682556501898787194739 108430023834752848180792109)
  ·
    refine ⟨40661258938032318067797041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108430023834752848180792109 40661258938032318067797041)
    ·
      refine ⟨30495944203524238550847781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40661258938032318067797041 30495944203524238550847781)
      ·
        refine ⟨5717989538160794728283959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30495944203524238550847781 5717989538160794728283959)
        ·
          refine ⟨8576984307241192092425939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5717989538160794728283959 8576984307241192092425939)
          ·
            refine ⟨12865476460861788138638909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8576984307241192092425939 12865476460861788138638909)
            ·
              refine ⟨4824553672823170551989591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12865476460861788138638909 4824553672823170551989591)
              ·
                refine ⟨7236830509234755827984387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824553672823170551989591 7236830509234755827984387)
                ·
                  refine ⟨10855245763852133741976581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7236830509234755827984387 10855245763852133741976581)
                  ·
                    refine ⟨2035358580722275076620609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10855245763852133741976581 2035358580722275076620609)
                    ·
                      refine ⟨1526518935541706307465457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035358580722275076620609 1526518935541706307465457)
                      ·
                        rfl

theorem cell23_2972885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_2972885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972885 prefixEnd_2972885 := by exact prefixLift 2972885
  have htrace : WordTrace (prefixWord ++ tailWord_2972885) baseStart_2972885 baseEnd_2972885 := by
    simpa [prefixWord, tailWord_2972885, baseEnd_2972885] using wordTrace_append hprefix tailTrace_2972885
  have hstable : (prefixWord ++ tailWord_2972885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972885).length < 2 ^ (prefixWord ++ tailWord_2972885).sum := by decide
  have hdescent : baseEnd_2972885 < baseStart_2972885 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972908 : List Nat := [2, 2, 1, 1, 2, 4, 3, 3, 5]
def baseStart_2972908 : Nat := 118140960795 + 2972908 * 2 ^ 59
def prefixEnd_2972908 : Nat := 4983230072969 + 3 ^ 40 * 2972908 * 2
def baseEnd_2972908 : Nat := 169614527288528857497539

theorem tailTrace_2972908 : CollatzResearch.WordTrace tailWord_2972908 prefixEnd_2972908 169614527288528857497539 := by
  unfold tailWord_2972908
  simp only [CollatzResearch.WordTrace]
  refine ⟨54215431356834761554439689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72287241809113015405919585 54215431356834761554439689)
  ·
    refine ⟨40661573517626071165829767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54215431356834761554439689 40661573517626071165829767)
    ·
      refine ⟨60992360276439106748744651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40661573517626071165829767 60992360276439106748744651)
      ·
        refine ⟨91488540414658660123116977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60992360276439106748744651 91488540414658660123116977)
        ·
          refine ⟨68616405310993995092337733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91488540414658660123116977 68616405310993995092337733)
          ·
            refine ⟨12865575995811374079813325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68616405310993995092337733 12865575995811374079813325)
            ·
              refine ⟨4824590998429265279929997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12865575995811374079813325 4824590998429265279929997)
              ·
                refine ⟨1809221624410974479973749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4824590998429265279929997 1809221624410974479973749)
                ·
                  refine ⟨169614527288528857497539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1809221624410974479973749 169614527288528857497539)
                  ·
                    rfl

theorem cell23_2972908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 3, 5].length) (baseStart_2972908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972908 prefixEnd_2972908 := by exact prefixLift 2972908
  have htrace : WordTrace (prefixWord ++ tailWord_2972908) baseStart_2972908 baseEnd_2972908 := by
    simpa [prefixWord, tailWord_2972908, baseEnd_2972908] using wordTrace_append hprefix tailTrace_2972908
  have hstable : (prefixWord ++ tailWord_2972908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972908).length < 2 ^ (prefixWord ++ tailWord_2972908).sum := by decide
  have hdescent : baseEnd_2972908 < baseStart_2972908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972921 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 2, 5]
def baseStart_2972921 : Nat := 118140960795 + 2972921 * 2 ^ 59
def prefixEnd_2972921 : Nat := 4983230072969 + 3 ^ 40 * 2972921 * 2
def baseEnd_2972921 : Nat := 508845806948422722205097

theorem tailTrace_2972921 : CollatzResearch.WordTrace tailWord_2972921 prefixEnd_2972921 508845806948422722205097 := by
  unfold tailWord_2972921
  simp only [CollatzResearch.WordTrace]
  refine ⟨108431336862622426329102617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72287557908414950886068411 108431336862622426329102617)
  ·
    refine ⟨81323502646966819746826963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108431336862622426329102617 81323502646966819746826963)
    ·
      refine ⟨121985253970450229620240445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81323502646966819746826963 121985253970450229620240445)
      ·
        refine ⟨45744470238918836107590167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 121985253970450229620240445 45744470238918836107590167)
        ·
          refine ⟨68616705358378254161385251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45744470238918836107590167 68616705358378254161385251)
          ·
            refine ⟨102925058037567381242077877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68616705358378254161385251 102925058037567381242077877)
            ·
              refine ⟨9649224191021941991444801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102925058037567381242077877 9649224191021941991444801)
              ·
                refine ⟨7236918143266456493583601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9649224191021941991444801 7236918143266456493583601)
                ·
                  refine ⟨5427688607449842370187701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7236918143266456493583601 5427688607449842370187701)
                  ·
                    refine ⟨508845806948422722205097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5427688607449842370187701 508845806948422722205097)
                    ·
                      rfl

theorem cell23_2972921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 5].length) (baseStart_2972921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972921 prefixEnd_2972921 := by exact prefixLift 2972921
  have htrace : WordTrace (prefixWord ++ tailWord_2972921) baseStart_2972921 baseEnd_2972921 := by
    simpa [prefixWord, tailWord_2972921, baseEnd_2972921] using wordTrace_append hprefix tailTrace_2972921
  have hstable : (prefixWord ++ tailWord_2972921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972921).length < 2 ^ (prefixWord ++ tailWord_2972921).sum := by decide
  have hdescent : baseEnd_2972921 < baseStart_2972921 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972931 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5]
def baseStart_2972931 : Nat := 118140960795 + 2972931 * 2 ^ 59
def prefixEnd_2972931 : Nat := 4983230072969 + 3 ^ 40 * 2972931 * 2
def baseEnd_2972931 : Nat := 1526542555651813127490245

theorem tailTrace_2972931 : CollatzResearch.WordTrace tailWord_2972931 prefixEnd_2972931 1526542555651813127490245 := by
  unfold tailWord_2972931
  simp only [CollatzResearch.WordTrace]
  refine ⟨108431701592586198036966647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72287801061724132024644431 108431701592586198036966647)
  ·
    refine ⟨162647552388879297055449971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108431701592586198036966647 162647552388879297055449971)
    ·
      refine ⟨243971328583318945583174957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162647552388879297055449971 243971328583318945583174957)
      ·
        refine ⟨91489248218744604593690609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 243971328583318945583174957 91489248218744604593690609)
        ·
          refine ⟨68616936164058453445267957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91489248218744604593690609 68616936164058453445267957)
          ·
            refine ⟨6432837765380480010493871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 68616936164058453445267957 6432837765380480010493871)
            ·
              refine ⟨9649256648070720015740807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6432837765380480010493871 9649256648070720015740807)
              ·
                refine ⟨14473884972106080023611211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9649256648070720015740807 14473884972106080023611211)
                ·
                  refine ⟨21710827458159120035416817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14473884972106080023611211 21710827458159120035416817)
                  ·
                    refine ⟨16283120593619340026562613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21710827458159120035416817 16283120593619340026562613)
                    ·
                      refine ⟨1526542555651813127490245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16283120593619340026562613 1526542555651813127490245)
                      ·
                        rfl

theorem cell23_2972931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 1, 2, 5].length) (baseStart_2972931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972931 prefixEnd_2972931 := by exact prefixLift 2972931
  have htrace : WordTrace (prefixWord ++ tailWord_2972931) baseStart_2972931 baseEnd_2972931 := by
    simpa [prefixWord, tailWord_2972931, baseEnd_2972931] using wordTrace_append hprefix tailTrace_2972931
  have hstable : (prefixWord ++ tailWord_2972931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972931).length < 2 ^ (prefixWord ++ tailWord_2972931).sum := by decide
  have hdescent : baseEnd_2972931 < baseStart_2972931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972936 : List Nat := [2, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2]
def baseStart_2972936 : Nat := 118140960795 + 2972936 * 2 ^ 59
def prefixEnd_2972936 : Nat := 4983230072969 + 3 ^ 40 * 2972936 * 2
def baseEnd_2972936 : Nat := 1526545123055085607927723

theorem tailTrace_2972936 : CollatzResearch.WordTrace tailWord_2972936 prefixEnd_2972936 1526545123055085607927723 := by
  unfold tailWord_2972936
  simp only [CollatzResearch.WordTrace]
  refine ⟨54215941978784041945449331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72287922638378722593932441 54215941978784041945449331)
  ·
    refine ⟨81323912968176062918173997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54215941978784041945449331 81323912968176062918173997)
    ·
      refine ⟨30496467363066023594315249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81323912968176062918173997 30496467363066023594315249)
      ·
        refine ⟨22872350522299517695736437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30496467363066023594315249 22872350522299517695736437)
        ·
          refine ⟨2144282861465579783975291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22872350522299517695736437 2144282861465579783975291)
          ·
            refine ⟨3216424292198369675962937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144282861465579783975291 3216424292198369675962937)
            ·
              refine ⟨2412318219148777256972203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216424292198369675962937 2412318219148777256972203)
              ·
                refine ⟨3618477328723165885458305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412318219148777256972203 3618477328723165885458305)
                ·
                  refine ⟨2713857996542374414093729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618477328723165885458305 2713857996542374414093729)
                  ·
                    refine ⟨2035393497406780810570297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2713857996542374414093729 2035393497406780810570297)
                    ·
                      refine ⟨1526545123055085607927723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035393497406780810570297 1526545123055085607927723)
                      ·
                        rfl

theorem cell23_2972936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 5, 1, 2, 1, 2, 2, 2].length) (baseStart_2972936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972936 prefixEnd_2972936 := by exact prefixLift 2972936
  have htrace : WordTrace (prefixWord ++ tailWord_2972936) baseStart_2972936 baseEnd_2972936 := by
    simpa [prefixWord, tailWord_2972936, baseEnd_2972936] using wordTrace_append hprefix tailTrace_2972936
  have hstable : (prefixWord ++ tailWord_2972936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972936).length < 2 ^ (prefixWord ++ tailWord_2972936).sum := by decide
  have hdescent : baseEnd_2972936 < baseStart_2972936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2972944 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9]
def baseStart_2972944 : Nat := 118140960795 + 2972944 * 2 ^ 59
def prefixEnd_2972944 : Nat := 4983230072969 + 3 ^ 40 * 2972944 * 2
def baseEnd_2972944 : Nat := 1526549230900321576627685

theorem tailTrace_2972944 : CollatzResearch.WordTrace tailWord_2972944 prefixEnd_2972944 1526549230900321576627685 := by
  unfold tailWord_2972944
  simp only [CollatzResearch.WordTrace]
  refine ⟨54216087870769550628594943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72288117161026067504793257 54216087870769550628594943)
  ·
    refine ⟨81324131806154325942892415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54216087870769550628594943 81324131806154325942892415)
    ·
      refine ⟨121986197709231488914338623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81324131806154325942892415 121986197709231488914338623)
      ·
        refine ⟨182979296563847233371507935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121986197709231488914338623 182979296563847233371507935)
        ·
          refine ⟨274468944845770850057261903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182979296563847233371507935 274468944845770850057261903)
          ·
            refine ⟨411703417268656275085892855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274468944845770850057261903 411703417268656275085892855)
            ·
              refine ⟨617555125902984412628839283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411703417268656275085892855 617555125902984412628839283)
              ·
                refine ⟨926332688854476618943258925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 617555125902984412628839283 926332688854476618943258925)
                ·
                  refine ⟨347374758320428732103722097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 926332688854476618943258925 347374758320428732103722097)
                  ·
                    refine ⟨260531068740321549077791573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 347374758320428732103722097 260531068740321549077791573)
                    ·
                      refine ⟨1526549230900321576627685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 260531068740321549077791573 1526549230900321576627685)
                      ·
                        rfl

theorem cell23_2972944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 9].length) (baseStart_2972944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2972944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2972944 prefixEnd_2972944 := by exact prefixLift 2972944
  have htrace : WordTrace (prefixWord ++ tailWord_2972944) baseStart_2972944 baseEnd_2972944 := by
    simpa [prefixWord, tailWord_2972944, baseEnd_2972944] using wordTrace_append hprefix tailTrace_2972944
  have hstable : (prefixWord ++ tailWord_2972944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2972944).length < 2 ^ (prefixWord ++ tailWord_2972944).sum := by decide
  have hdescent : baseEnd_2972944 < baseStart_2972944 := by decide
  rcases family_descends (prefixWord ++ tailWord_2972944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973011 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 3, 5]
def baseStart_2973011 : Nat := 118140960795 + 2973011 * 2 ^ 59
def prefixEnd_2973011 : Nat := 4983230072969 + 3 ^ 40 * 2973011 * 2
def baseEnd_2973011 : Nat := 508861211368057604829959

theorem tailTrace_2973011 : CollatzResearch.WordTrace tailWord_2973011 prefixEnd_2973011 508861211368057604829959 := by
  unfold tailWord_2973011
  simp only [CollatzResearch.WordTrace]
  refine ⟨108434619432296371699878887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72289746288197581133252591 108434619432296371699878887)
  ·
    refine ⟨162651929148444557549818331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108434619432296371699878887 162651929148444557549818331)
    ·
      refine ⟨243977893722666836324727497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162651929148444557549818331 243977893722666836324727497)
      ·
        refine ⟨182983420292000127243545623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 243977893722666836324727497 182983420292000127243545623)
        ·
          refine ⟨274475130438000190865318435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 182983420292000127243545623 274475130438000190865318435)
          ·
            refine ⟨411712695657000286297977653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274475130438000190865318435 411712695657000286297977653)
            ·
              refine ⟨38598065217843776840435405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 411712695657000286297977653 38598065217843776840435405)
              ·
                refine ⟨14474274456691416315163277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38598065217843776840435405 14474274456691416315163277)
                ·
                  refine ⟨5427852921259281118186229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14474274456691416315163277 5427852921259281118186229)
                  ·
                    refine ⟨508861211368057604829959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5427852921259281118186229 508861211368057604829959)
                    ·
                      rfl

theorem cell23_2973011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 3, 5].length) (baseStart_2973011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973011 prefixEnd_2973011 := by exact prefixLift 2973011
  have htrace : WordTrace (prefixWord ++ tailWord_2973011) baseStart_2973011 baseEnd_2973011 := by
    simpa [prefixWord, tailWord_2973011, baseEnd_2973011] using wordTrace_append hprefix tailTrace_2973011
  have hstable : (prefixWord ++ tailWord_2973011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973011).length < 2 ^ (prefixWord ++ tailWord_2973011).sum := by decide
  have hdescent : baseEnd_2973011 < baseStart_2973011 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973032 : List Nat := [2, 1, 4, 2, 4, 1, 1, 2, 6]
def baseStart_2973032 : Nat := 118140960795 + 2973032 * 2 ^ 59
def prefixEnd_2973032 : Nat := 4983230072969 + 3 ^ 40 * 2973032 * 2
def baseEnd_2973032 : Nat := 169621601910879692480809

theorem tailTrace_2973032 : CollatzResearch.WordTrace tailWord_2973032 prefixEnd_2973032 169621601910879692480809 := by
  unfold tailWord_2973032
  simp only [CollatzResearch.WordTrace]
  refine ⟨54217692682610146143196675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72290256910146861524262233 54217692682610146143196675)
  ·
    refine ⟨81326539023915219214795013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54217692682610146143196675 81326539023915219214795013)
    ·
      refine ⟨15248726066984103602774065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81326539023915219214795013 15248726066984103602774065)
      ·
        refine ⟨11436544550238077702080549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15248726066984103602774065 11436544550238077702080549)
        ·
          refine ⟨2144352103169639569140103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11436544550238077702080549 2144352103169639569140103)
          ·
            refine ⟨3216528154754459353710155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2144352103169639569140103 3216528154754459353710155)
            ·
              refine ⟨4824792232131689030565233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216528154754459353710155 4824792232131689030565233)
              ·
                refine ⟨3618594174098766772923925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824792232131689030565233 3618594174098766772923925)
                ·
                  refine ⟨169621601910879692480809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3618594174098766772923925 169621601910879692480809)
                  ·
                    rfl

theorem cell23_2973032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 6].length) (baseStart_2973032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973032 prefixEnd_2973032 := by exact prefixLift 2973032
  have htrace : WordTrace (prefixWord ++ tailWord_2973032) baseStart_2973032 baseEnd_2973032 := by
    simpa [prefixWord, tailWord_2973032, baseEnd_2973032] using wordTrace_append hprefix tailTrace_2973032
  have hstable : (prefixWord ++ tailWord_2973032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973032).length < 2 ^ (prefixWord ++ tailWord_2973032).sum := by decide
  have hdescent : baseEnd_2973032 < baseStart_2973032 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973041 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 3, 6]
def baseStart_2973041 : Nat := 118140960795 + 2973041 * 2 ^ 59
def prefixEnd_2973041 : Nat := 4983230072969 + 3 ^ 40 * 2973041 * 2
def baseEnd_2973041 : Nat := 508866346174602565704913

theorem tailTrace_2973041 : CollatzResearch.WordTrace tailWord_2973041 prefixEnd_2973041 508866346174602565704913 := by
  unfold tailWord_2973041
  simp only [CollatzResearch.WordTrace]
  refine ⟨108435713622187686823470977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72290475748125124548980651 108435713622187686823470977)
  ·
    refine ⟨81326785216640765117603233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108435713622187686823470977 81326785216640765117603233)
    ·
      refine ⟨60995088912480573838202425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81326785216640765117603233 60995088912480573838202425)
      ·
        refine ⟨45746316684360430378651819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60995088912480573838202425 45746316684360430378651819)
        ·
          refine ⟨68619475026540645567977729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45746316684360430378651819 68619475026540645567977729)
          ·
            refine ⟨51464606269905484175983297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68619475026540645567977729 51464606269905484175983297)
            ·
              refine ⟨38598454702429113131987473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51464606269905484175983297 38598454702429113131987473)
              ·
                refine ⟨28948841026821834848990605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38598454702429113131987473 28948841026821834848990605)
                ·
                  refine ⟨10855815385058188068371477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28948841026821834848990605 10855815385058188068371477)
                  ·
                    refine ⟨508866346174602565704913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10855815385058188068371477 508866346174602565704913)
                    ·
                      rfl

theorem cell23_2973041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 6].length) (baseStart_2973041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973041 prefixEnd_2973041 := by exact prefixLift 2973041
  have htrace : WordTrace (prefixWord ++ tailWord_2973041) baseStart_2973041 baseEnd_2973041 := by
    simpa [prefixWord, tailWord_2973041, baseEnd_2973041] using wordTrace_append hprefix tailTrace_2973041
  have hstable : (prefixWord ++ tailWord_2973041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973041).length < 2 ^ (prefixWord ++ tailWord_2973041).sum := by decide
  have hdescent : baseEnd_2973041 < baseStart_2973041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973042 : List Nat := [3, 2, 1, 2, 1, 2, 1, 6, 1, 1, 3]
def baseStart_2973042 : Nat := 118140960795 + 2973042 * 2 ^ 59
def prefixEnd_2973042 : Nat := 4983230072969 + 3 ^ 40 * 2973042 * 2
def baseEnd_2973042 : Nat := 1526599552004462193202235

theorem tailTrace_2973042 : CollatzResearch.WordTrace tailWord_2973042 prefixEnd_2973042 1526599552004462193202235 := by
  unfold tailWord_2973042
  simp only [CollatzResearch.WordTrace]
  refine ⟨27108937523796015998564345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72290500063456042662838253 27108937523796015998564345)
  ·
    refine ⟨20331703142847011998923259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27108937523796015998564345 20331703142847011998923259)
    ·
      refine ⟨30497554714270517998384889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20331703142847011998923259 30497554714270517998384889)
      ·
        refine ⟨22873166035702888498788667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30497554714270517998384889 22873166035702888498788667)
        ·
          refine ⟨34309749053554332748183001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22873166035702888498788667 34309749053554332748183001)
          ·
            refine ⟨25732311790165749561137251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34309749053554332748183001 25732311790165749561137251)
            ·
              refine ⟨38598467685248624341705877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25732311790165749561137251 38598467685248624341705877)
              ·
                refine ⟨1809303172746029266017463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 38598467685248624341705877 1809303172746029266017463)
                ·
                  refine ⟨2713954759119043899026195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809303172746029266017463 2713954759119043899026195)
                  ·
                    refine ⟨4070932138678565848539293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713954759119043899026195 4070932138678565848539293)
                    ·
                      refine ⟨1526599552004462193202235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070932138678565848539293 1526599552004462193202235)
                      ·
                        rfl

theorem cell23_2973042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 1, 6, 1, 1, 3].length) (baseStart_2973042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973042 prefixEnd_2973042 := by exact prefixLift 2973042
  have htrace : WordTrace (prefixWord ++ tailWord_2973042) baseStart_2973042 baseEnd_2973042 := by
    simpa [prefixWord, tailWord_2973042, baseEnd_2973042] using wordTrace_append hprefix tailTrace_2973042
  have hstable : (prefixWord ++ tailWord_2973042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973042).length < 2 ^ (prefixWord ++ tailWord_2973042).sum := by decide
  have hdescent : baseEnd_2973042 < baseStart_2973042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973076 : List Nat := [2, 4, 2, 1, 2, 3, 1, 3, 1, 1, 3]
def baseStart_2973076 : Nat := 118140960795 + 2973076 * 2 ^ 59
def prefixEnd_2973076 : Nat := 4983230072969 + 3 ^ 40 * 2973076 * 2
def baseEnd_2973076 : Nat := 1526617010346715060177079

theorem tailTrace_2973076 : CollatzResearch.WordTrace tailWord_2973076 prefixEnd_2973076 1526617010346715060177079 := by
  unfold tailWord_2973076
  simp only [CollatzResearch.WordTrace]
  refine ⟨54218495088530443900497541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72291326784707258533996721 54218495088530443900497541)
  ·
    refine ⟨10165967829099458231343289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54218495088530443900497541 10165967829099458231343289)
    ·
      refine ⟨7624475871824593673507467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10165967829099458231343289 7624475871824593673507467)
      ·
        refine ⟨11436713807736890510261201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624475871824593673507467 11436713807736890510261201)
        ·
          refine ⟨8577535355802667882695901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11436713807736890510261201 8577535355802667882695901)
          ·
            refine ⟨3216575758426000456010963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8577535355802667882695901 3216575758426000456010963)
            ·
              refine ⟨4824863637639000684016445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216575758426000456010963 4824863637639000684016445)
              ·
                refine ⟨1809323864114625256506167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4824863637639000684016445 1809323864114625256506167)
                ·
                  refine ⟨2713985796171937884759251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809323864114625256506167 2713985796171937884759251)
                  ·
                    refine ⟨4070978694257906827138877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2713985796171937884759251 4070978694257906827138877)
                    ·
                      refine ⟨1526617010346715060177079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4070978694257906827138877 1526617010346715060177079)
                      ·
                        rfl

theorem cell23_2973076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 3, 1, 3, 1, 1, 3].length) (baseStart_2973076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973076 prefixEnd_2973076 := by exact prefixLift 2973076
  have htrace : WordTrace (prefixWord ++ tailWord_2973076) baseStart_2973076 baseEnd_2973076 := by
    simpa [prefixWord, tailWord_2973076, baseEnd_2973076] using wordTrace_append hprefix tailTrace_2973076
  have hstable : (prefixWord ++ tailWord_2973076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973076).length < 2 ^ (prefixWord ++ tailWord_2973076).sum := by decide
  have hdescent : baseEnd_2973076 < baseStart_2973076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973085 : List Nat := [1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_2973085 : Nat := 118140960795 + 2973085 * 2 ^ 59
def prefixEnd_2973085 : Nat := 4983230072969 + 3 ^ 40 * 2973085 * 2
def baseEnd_2973085 : Nat := 1526621631672605524964537

theorem tailTrace_2973085 : CollatzResearch.WordTrace tailWord_2973085 prefixEnd_2973085 1526621631672605524964537 := by
  unfold tailWord_2973085
  simp only [CollatzResearch.WordTrace]
  refine ⟨108437318434028282338072709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72291545622685521558715139 108437318434028282338072709)
  ·
    refine ⟨20331997206380302938388633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108437318434028282338072709 20331997206380302938388633)
    ·
      refine ⟨15248997904785227203791475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20331997206380302938388633 15248997904785227203791475)
      ·
        refine ⟨22873496857177840805687213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15248997904785227203791475 22873496857177840805687213)
        ·
          refine ⟨8577561321441690302132705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22873496857177840805687213 8577561321441690302132705)
          ·
            refine ⟨6433170991081267726599529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8577561321441690302132705 6433170991081267726599529)
            ·
              refine ⟨4824878243310950794949647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6433170991081267726599529 4824878243310950794949647)
              ·
                refine ⟨7237317364966426192424471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4824878243310950794949647 7237317364966426192424471)
                ·
                  refine ⟨10855976047449639288636707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7237317364966426192424471 10855976047449639288636707)
                  ·
                    refine ⟨16283964071174458932955061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10855976047449639288636707 16283964071174458932955061)
                    ·
                      refine ⟨1526621631672605524964537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16283964071174458932955061 1526621631672605524964537)
                      ·
                        rfl

theorem cell23_2973085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_2973085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973085 prefixEnd_2973085 := by exact prefixLift 2973085
  have htrace : WordTrace (prefixWord ++ tailWord_2973085) baseStart_2973085 baseEnd_2973085 := by
    simpa [prefixWord, tailWord_2973085, baseEnd_2973085] using wordTrace_append hprefix tailTrace_2973085
  have hstable : (prefixWord ++ tailWord_2973085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973085).length < 2 ^ (prefixWord ++ tailWord_2973085).sum := by decide
  have hdescent : baseEnd_2973085 < baseStart_2973085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973109 : List Nat := [1, 3, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_2973109 : Nat := 118140960795 + 2973109 * 2 ^ 59
def prefixEnd_2973109 : Nat := 4983230072969 + 3 ^ 40 * 2973109 * 2
def baseEnd_2973109 : Nat := 508877985069437810354809

theorem tailTrace_2973109 : CollatzResearch.WordTrace tailWord_2973109 prefixEnd_2973109 508877985069437810354809 := by
  unfold tailWord_2973109
  simp only [CollatzResearch.WordTrace]
  refine ⟨108438193785941334436946381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72292129190627556291297587 108438193785941334436946381)
  ·
    refine ⟨40664322669728000413854893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108438193785941334436946381 40664322669728000413854893)
    ·
      refine ⟨15249121001148000155195585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40664322669728000413854893 15249121001148000155195585)
      ·
        refine ⟨11436840750861000116396689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15249121001148000155195585 11436840750861000116396689)
        ·
          refine ⟨8577630563145750087297517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11436840750861000116396689 8577630563145750087297517)
          ·
            refine ⟨3216611461179656282736569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8577630563145750087297517 3216611461179656282736569)
            ·
              refine ⟨2412458595884742212052427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216611461179656282736569 2412458595884742212052427)
              ·
                refine ⟨3618687893827113318078641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412458595884742212052427 3618687893827113318078641)
                ·
                  refine ⟨2714015920370334988558981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618687893827113318078641 2714015920370334988558981)
                  ·
                    refine ⟨508877985069437810354809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714015920370334988558981 508877985069437810354809)
                    ·
                      rfl

theorem cell23_2973109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_2973109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973109 prefixEnd_2973109 := by exact prefixLift 2973109
  have htrace : WordTrace (prefixWord ++ tailWord_2973109) baseStart_2973109 baseEnd_2973109 := by
    simpa [prefixWord, tailWord_2973109, baseEnd_2973109] using wordTrace_append hprefix tailTrace_2973109
  have hstable : (prefixWord ++ tailWord_2973109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973109).length < 2 ^ (prefixWord ++ tailWord_2973109).sum := by decide
  have hdescent : baseEnd_2973109 < baseStart_2973109 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973149 : List Nat := [1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_2973149 : Nat := 118140960795 + 2973149 * 2 ^ 59
def prefixEnd_2973149 : Nat := 4983230072969 + 3 ^ 40 * 2973149 * 2
def baseEnd_2973149 : Nat := 1526654494434493274564243

theorem tailTrace_2973149 : CollatzResearch.WordTrace tailWord_2973149 prefixEnd_2973149 1526654494434493274564243 := by
  unfold tailWord_2973149
  simp only [CollatzResearch.WordTrace]
  refine ⟨108439652705796421268402501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72293101803864280845601667 108439652705796421268402501)
  ·
    refine ⟨20332434882336828987825469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108439652705796421268402501 20332434882336828987825469)
    ·
      refine ⟨7624663080876310870434551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20332434882336828987825469 7624663080876310870434551)
      ·
        refine ⟨11436994621314466305651827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7624663080876310870434551 11436994621314466305651827)
        ·
          refine ⟨17155491931971699458477741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11436994621314466305651827 17155491931971699458477741)
          ·
            refine ⟨6433309474489387296929153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17155491931971699458477741 6433309474489387296929153)
            ·
              refine ⟨4824982105867040472696865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6433309474489387296929153 4824982105867040472696865)
              ·
                refine ⟨3618736579400280354522649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4824982105867040472696865 3618736579400280354522649)
                ·
                  refine ⟨2714052434550210265891987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3618736579400280354522649 2714052434550210265891987)
                  ·
                    refine ⟨4071078651825315398837981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2714052434550210265891987 4071078651825315398837981)
                    ·
                      refine ⟨1526654494434493274564243, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4071078651825315398837981 1526654494434493274564243)
                      ·
                        rfl

theorem cell23_2973149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_2973149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973149 prefixEnd_2973149 := by exact prefixLift 2973149
  have htrace : WordTrace (prefixWord ++ tailWord_2973149) baseStart_2973149 baseEnd_2973149 := by
    simpa [prefixWord, tailWord_2973149, baseEnd_2973149] using wordTrace_append hprefix tailTrace_2973149
  have hstable : (prefixWord ++ tailWord_2973149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973149).length < 2 ^ (prefixWord ++ tailWord_2973149).sum := by decide
  have hdescent : baseEnd_2973149 < baseStart_2973149 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973168 : List Nat := [2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4]
def baseStart_2973168 : Nat := 118140960795 + 2973168 * 2 ^ 59
def prefixEnd_2973168 : Nat := 4983230072969 + 3 ^ 40 * 2973168 * 2
def baseEnd_2973168 : Nat := 1526664250566928700226655

theorem tailTrace_2973168 : CollatzResearch.WordTrace tailWord_2973168 prefixEnd_2973168 1526664250566928700226655 := by
  unfold tailWord_2973168
  simp only [CollatzResearch.WordTrace]
  refine ⟨54220172846363793756672079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72293563795151725008896105 54220172846363793756672079)
  ·
    refine ⟨81330259269545690635008119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54220172846363793756672079 81330259269545690635008119)
    ·
      refine ⟨121995388904318535952512179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81330259269545690635008119 121995388904318535952512179)
      ·
        refine ⟨182993083356477803928768269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 121995388904318535952512179 182993083356477803928768269)
        ·
          refine ⟨68622406258679176473288101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 182993083356477803928768269 68622406258679176473288101)
          ·
            refine ⟨12866701173502345588741519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 68622406258679176473288101 12866701173502345588741519)
            ·
              refine ⟨19300051760253518383112279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12866701173502345588741519 19300051760253518383112279)
              ·
                refine ⟨28950077640380277574668419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19300051760253518383112279 28950077640380277574668419)
                ·
                  refine ⟨43425116460570416362002629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28950077640380277574668419 43425116460570416362002629)
                  ·
                    refine ⟨8142209336356953067875493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43425116460570416362002629 8142209336356953067875493)
                    ·
                      refine ⟨1526664250566928700226655, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8142209336356953067875493 1526664250566928700226655)
                      ·
                        rfl

theorem cell23_2973168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 1, 1, 4, 4].length) (baseStart_2973168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973168 prefixEnd_2973168 := by exact prefixLift 2973168
  have htrace : WordTrace (prefixWord ++ tailWord_2973168) baseStart_2973168 baseEnd_2973168 := by
    simpa [prefixWord, tailWord_2973168, baseEnd_2973168] using wordTrace_append hprefix tailTrace_2973168
  have hstable : (prefixWord ++ tailWord_2973168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973168).length < 2 ^ (prefixWord ++ tailWord_2973168).sum := by decide
  have hdescent : baseEnd_2973168 < baseStart_2973168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973178 : List Nat := [3, 1, 1, 1, 1, 2, 5, 2, 7]
def baseStart_2973178 : Nat := 118140960795 + 2973178 * 2 ^ 59
def prefixEnd_2973178 : Nat := 4983230072969 + 3 ^ 40 * 2973178 * 2
def baseEnd_2973178 : Nat := 169629931708163740122401

theorem tailTrace_2973178 : CollatzResearch.WordTrace tailWord_2973178 prefixEnd_2973178 169629931708163740122401 := by
  unfold tailWord_2973178
  simp only [CollatzResearch.WordTrace]
  refine ⟨27110177605672839805302047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72293806948460906147472125 27110177605672839805302047)
  ·
    refine ⟨40665266408509259707953071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27110177605672839805302047 40665266408509259707953071)
    ·
      refine ⟨60997899612763889561929607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40665266408509259707953071 60997899612763889561929607)
      ·
        refine ⟨91496849419145834342894411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60997899612763889561929607 91496849419145834342894411)
        ·
          refine ⟨137245274128718751514341617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91496849419145834342894411 137245274128718751514341617)
          ·
            refine ⟨102933955596539063635756213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137245274128718751514341617 102933955596539063635756213)
            ·
              refine ⟨9650058337175537215852145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102933955596539063635756213 9650058337175537215852145)
              ·
                refine ⟨7237543752881652911889109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9650058337175537215852145 7237543752881652911889109)
                ·
                  refine ⟨169629931708163740122401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7237543752881652911889109 169629931708163740122401)
                  ·
                    rfl

theorem cell23_2973178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 5, 2, 7].length) (baseStart_2973178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973178 prefixEnd_2973178 := by exact prefixLift 2973178
  have htrace : WordTrace (prefixWord ++ tailWord_2973178) baseStart_2973178 baseEnd_2973178 := by
    simpa [prefixWord, tailWord_2973178, baseEnd_2973178] using wordTrace_append hprefix tailTrace_2973178
  have hstable : (prefixWord ++ tailWord_2973178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973178).length < 2 ^ (prefixWord ++ tailWord_2973178).sum := by decide
  have hdescent : baseEnd_2973178 < baseStart_2973178 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973205 : List Nat := [1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 3]
def baseStart_2973205 : Nat := 118140960795 + 2973205 * 2 ^ 59
def prefixEnd_2973205 : Nat := 4983230072969 + 3 ^ 40 * 2973205 * 2
def baseEnd_2973205 : Nat := 1526683249351145055463985

theorem tailTrace_2973205 : CollatzResearch.WordTrace tailWord_2973205 prefixEnd_2973205 1526683249351145055463985 := by
  unfold tailWord_2973205
  simp only [CollatzResearch.WordTrace]
  refine ⟨108441695193593542832441069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72294463462395695221627379 108441695193593542832441069)
  ·
    refine ⟨40665635697597578562165401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108441695193593542832441069 40665635697597578562165401)
    ·
      refine ⟨30499226773198183921624051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40665635697597578562165401 30499226773198183921624051)
      ·
        refine ⟨45748840159797275882436077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30499226773198183921624051 45748840159797275882436077)
        ·
          refine ⟨17155815059923978455913529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45748840159797275882436077 17155815059923978455913529)
          ·
            refine ⟨12866861294942983841935147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17155815059923978455913529 12866861294942983841935147)
            ·
              refine ⟨19300291942414475762902721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12866861294942983841935147 19300291942414475762902721)
              ·
                refine ⟨14475218956810856822177041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19300291942414475762902721 14475218956810856822177041)
                ·
                  refine ⟨10856414217608142616632781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14475218956810856822177041 10856414217608142616632781)
                  ·
                    refine ⟨4071155331603053481237293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10856414217608142616632781 4071155331603053481237293)
                    ·
                      refine ⟨1526683249351145055463985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4071155331603053481237293 1526683249351145055463985)
                      ·
                        rfl

theorem cell23_2973205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 2, 1, 2, 2, 3, 3].length) (baseStart_2973205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973205 prefixEnd_2973205 := by exact prefixLift 2973205
  have htrace : WordTrace (prefixWord ++ tailWord_2973205) baseStart_2973205 baseEnd_2973205 := by
    simpa [prefixWord, tailWord_2973205, baseEnd_2973205] using wordTrace_append hprefix tailTrace_2973205
  have hstable : (prefixWord ++ tailWord_2973205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973205).length < 2 ^ (prefixWord ++ tailWord_2973205).sum := by decide
  have hdescent : baseEnd_2973205 < baseStart_2973205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973215 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 1, 7, 2]
def baseStart_2973215 : Nat := 118140960795 + 2973215 * 2 ^ 59
def prefixEnd_2973215 : Nat := 4983230072969 + 3 ^ 40 * 2973215 * 2
def baseEnd_2973215 : Nat := 1526688384157690016338939

theorem tailTrace_2973215 : CollatzResearch.WordTrace tailWord_2973215 prefixEnd_2973215 1526688384157690016338939 := by
  unfold tailWord_2973215
  simp only [CollatzResearch.WordTrace]
  refine ⟨108442059923557314540305099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72294706615704876360203399 108442059923557314540305099)
  ·
    refine ⟨162663089885335971810457649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108442059923557314540305099 162663089885335971810457649)
    ·
      refine ⟨121997317414001978857843237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162663089885335971810457649 121997317414001978857843237)
      ·
        refine ⟨22874497015125371035845607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 121997317414001978857843237 22874497015125371035845607)
        ·
          refine ⟨34311745522688056553768411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22874497015125371035845607 34311745522688056553768411)
          ·
            refine ⟨51467618284032084830652617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34311745522688056553768411 51467618284032084830652617)
            ·
              refine ⟨38600713713024063622989463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51467618284032084830652617 38600713713024063622989463)
              ·
                refine ⟨57901070569536095434484195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38600713713024063622989463 57901070569536095434484195)
                ·
                  refine ⟨86851605854304143151726293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57901070569536095434484195 86851605854304143151726293)
                  ·
                    refine ⟨2035584512210253355118585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 86851605854304143151726293 2035584512210253355118585)
                    ·
                      refine ⟨1526688384157690016338939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035584512210253355118585 1526688384157690016338939)
                      ·
                        rfl

theorem cell23_2973215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 7, 2].length) (baseStart_2973215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973215 prefixEnd_2973215 := by exact prefixLift 2973215
  have htrace : WordTrace (prefixWord ++ tailWord_2973215) baseStart_2973215 baseEnd_2973215 := by
    simpa [prefixWord, tailWord_2973215, baseEnd_2973215] using wordTrace_append hprefix tailTrace_2973215
  have hstable : (prefixWord ++ tailWord_2973215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973215).length < 2 ^ (prefixWord ++ tailWord_2973215).sum := by decide
  have hdescent : baseEnd_2973215 < baseStart_2973215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973248 : List Nat := [2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5]
def baseStart_2973248 : Nat := 118140960795 + 2973248 * 2 ^ 59
def prefixEnd_2973248 : Nat := 4983230072969 + 3 ^ 40 * 2973248 * 2
def baseEnd_2973248 : Nat := 1526705329019288387226287

theorem tailTrace_2973248 : CollatzResearch.WordTrace tailWord_2973248 prefixEnd_2973248 1526705329019288387226287 := by
  unfold tailWord_2973248
  simp only [CollatzResearch.WordTrace]
  refine ⟨54221631766218880588128199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72295509021625174117504265 54221631766218880588128199)
  ·
    refine ⟨81332447649328320882192299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54221631766218880588128199 81332447649328320882192299)
    ·
      refine ⟨121998671473992481323288449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81332447649328320882192299 121998671473992481323288449)
      ·
        refine ⟨91499003605494360992466337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 121998671473992481323288449 91499003605494360992466337)
        ·
          refine ⟨68624252704120770744349753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91499003605494360992466337 68624252704120770744349753)
          ·
            refine ⟨51468189528090578058262315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68624252704120770744349753 51468189528090578058262315)
            ·
              refine ⟨77202284292135867087393473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51468189528090578058262315 77202284292135867087393473)
              ·
                refine ⟨57901713219101900315545105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77202284292135867087393473 57901713219101900315545105)
                ·
                  refine ⟨43426284914326425236658829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57901713219101900315545105 43426284914326425236658829)
                  ·
                    refine ⟨16284856842872409463747061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43426284914326425236658829 16284856842872409463747061)
                    ·
                      refine ⟨1526705329019288387226287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16284856842872409463747061 1526705329019288387226287)
                      ·
                        rfl

theorem cell23_2973248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 5].length) (baseStart_2973248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973248 prefixEnd_2973248 := by exact prefixLift 2973248
  have htrace : WordTrace (prefixWord ++ tailWord_2973248) baseStart_2973248 baseEnd_2973248 := by
    simpa [prefixWord, tailWord_2973248, baseEnd_2973248] using wordTrace_append hprefix tailTrace_2973248
  have hstable : (prefixWord ++ tailWord_2973248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973248).length < 2 ^ (prefixWord ++ tailWord_2973248).sum := by decide
  have hdescent : baseEnd_2973248 < baseStart_2973248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973366 : List Nat := [5, 1, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_2973366 : Nat := 118140960795 + 2973366 * 2 ^ 59
def prefixEnd_2973366 : Nat := 4983230072969 + 3 ^ 40 * 2973366 * 2
def baseEnd_2973366 : Nat := 508921973245506308516915

theorem tailTrace_2973366 : CollatzResearch.WordTrace tailWord_2973366 prefixEnd_2973366 508921973245506308516915 := by
  unfold tailWord_2973366
  simp only [CollatzResearch.WordTrace]
  refine ⟨6777972959125641708065747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72298378230673511552701301 6777972959125641708065747)
  ·
    refine ⟨10166959438688462562098621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6777972959125641708065747 10166959438688462562098621)
    ·
      refine ⟨3812609789508173460786983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10166959438688462562098621 3812609789508173460786983)
      ·
        refine ⟨5718914684262260191180475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812609789508173460786983 5718914684262260191180475)
        ·
          refine ⟨8578372026393390286770713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718914684262260191180475 8578372026393390286770713)
          ·
            refine ⟨6433779019795042715078035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578372026393390286770713 6433779019795042715078035)
            ·
              refine ⟨9650668529692564072617053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6433779019795042715078035 9650668529692564072617053)
              ·
                refine ⟨3619000698634711527231395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9650668529692564072617053 3619000698634711527231395)
                ·
                  refine ⟨5428501047952067290847093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619000698634711527231395 5428501047952067290847093)
                  ·
                    refine ⟨508921973245506308516915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5428501047952067290847093 508921973245506308516915)
                    ·
                      rfl

theorem cell23_2973366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_2973366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973366 prefixEnd_2973366 := by exact prefixLift 2973366
  have htrace : WordTrace (prefixWord ++ tailWord_2973366) baseStart_2973366 baseEnd_2973366 := by
    simpa [prefixWord, tailWord_2973366, baseEnd_2973366] using wordTrace_append hprefix tailTrace_2973366
  have hstable : (prefixWord ++ tailWord_2973366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973366).length < 2 ^ (prefixWord ++ tailWord_2973366).sum := by decide
  have hdescent : baseEnd_2973366 < baseStart_2973366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973369 : List Nat := [1, 2, 1, 4, 1, 1, 6, 1, 1, 1, 4]
def baseStart_2973369 : Nat := 118140960795 + 2973369 * 2 ^ 59
def prefixEnd_2973369 : Nat := 4983230072969 + 3 ^ 40 * 2973369 * 2
def baseEnd_2973369 : Nat := 1526767460178482413813231

theorem tailTrace_2973369 : CollatzResearch.WordTrace tailWord_2973369 prefixEnd_2973369 1526767460178482413813231 := by
  unfold tailWord_2973369
  simp only [CollatzResearch.WordTrace]
  refine ⟨108447676764999398841411161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72298451176666265894274107 108447676764999398841411161)
  ·
    refine ⟨81335757573749549131058371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108447676764999398841411161 81335757573749549131058371)
    ·
      refine ⟨122003636360624323696587557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81335757573749549131058371 122003636360624323696587557)
      ·
        refine ⟨22875681817617060693110167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 122003636360624323696587557 22875681817617060693110167)
        ·
          refine ⟨34313522726425591039665251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22875681817617060693110167 34313522726425591039665251)
          ·
            refine ⟨51470284089638386559497877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34313522726425591039665251 51470284089638386559497877)
            ·
              refine ⟨2412669566701799369976463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 51470284089638386559497877 2412669566701799369976463)
              ·
                refine ⟨3619004350052699054964695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412669566701799369976463 3619004350052699054964695)
                ·
                  refine ⟨5428506525079048582447043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619004350052699054964695 5428506525079048582447043)
                  ·
                    refine ⟨8142759787618572873670565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5428506525079048582447043 8142759787618572873670565)
                    ·
                      refine ⟨1526767460178482413813231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8142759787618572873670565 1526767460178482413813231)
                      ·
                        rfl

theorem cell23_2973369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 6, 1, 1, 1, 4].length) (baseStart_2973369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973369 prefixEnd_2973369 := by exact prefixLift 2973369
  have htrace : WordTrace (prefixWord ++ tailWord_2973369) baseStart_2973369 baseEnd_2973369 := by
    simpa [prefixWord, tailWord_2973369, baseEnd_2973369] using wordTrace_append hprefix tailTrace_2973369
  have hstable : (prefixWord ++ tailWord_2973369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973369).length < 2 ^ (prefixWord ++ tailWord_2973369).sum := by decide
  have hdescent : baseEnd_2973369 < baseStart_2973369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973385 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 3]
def baseStart_2973385 : Nat := 118140960795 + 2973385 * 2 ^ 59
def prefixEnd_2973385 : Nat := 4983230072969 + 3 ^ 40 * 2973385 * 2
def baseEnd_2973385 : Nat := 1526775675868954351213157

theorem tailTrace_2973385 : CollatzResearch.WordTrace tailWord_2973385 prefixEnd_2973385 1526775675868954351213157 := by
  unfold tailWord_2973385
  simp only [CollatzResearch.WordTrace]
  refine ⟨108448260332941433573993609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72298840221960955715995739 108448260332941433573993609)
  ·
    refine ⟨81336195249706075180495207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108448260332941433573993609 81336195249706075180495207)
    ·
      refine ⟨122004292874559112770742811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81336195249706075180495207 122004292874559112770742811)
      ·
        refine ⟨183006439311838669156114217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122004292874559112770742811 183006439311838669156114217)
        ·
          refine ⟨137254829483879001867085663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183006439311838669156114217 137254829483879001867085663)
          ·
            refine ⟨205882244225818502800628495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137254829483879001867085663 205882244225818502800628495)
            ·
              refine ⟨308823366338727754200942743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205882244225818502800628495 308823366338727754200942743)
              ·
                refine ⟨463235049508091631301414115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308823366338727754200942743 463235049508091631301414115)
                ·
                  refine ⟨694852574262137446952121173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463235049508091631301414115 694852574262137446952121173)
                  ·
                    refine ⟨4071401802317211603235085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 694852574262137446952121173 4071401802317211603235085)
                    ·
                      refine ⟨1526775675868954351213157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4071401802317211603235085 1526775675868954351213157)
                      ·
                        rfl

theorem cell23_2973385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 1, 9, 3].length) (baseStart_2973385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973385 prefixEnd_2973385 := by exact prefixLift 2973385
  have htrace : WordTrace (prefixWord ++ tailWord_2973385) baseStart_2973385 baseEnd_2973385 := by
    simpa [prefixWord, tailWord_2973385, baseEnd_2973385] using wordTrace_append hprefix tailTrace_2973385
  have hstable : (prefixWord ++ tailWord_2973385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973385).length < 2 ^ (prefixWord ++ tailWord_2973385).sum := by decide
  have hdescent : baseEnd_2973385 < baseStart_2973385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973389 : List Nat := [1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 5]
def baseStart_2973389 : Nat := 118140960795 + 2973389 * 2 ^ 59
def prefixEnd_2973389 : Nat := 4983230072969 + 3 ^ 40 * 2973389 * 2
def baseEnd_2973389 : Nat := 1526777729791572335563139

theorem tailTrace_2973389 : CollatzResearch.WordTrace tailWord_2973389 prefixEnd_2973389 1526777729791572335563139 := by
  unfold tailWord_2973389
  simp only [CollatzResearch.WordTrace]
  refine ⟨108448406224926942257139221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72298937483284628171426147 108448406224926942257139221)
  ·
    refine ⟨5083519041793450418303401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 108448406224926942257139221 5083519041793450418303401)
    ·
      refine ⟨3812639281345087813727551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5083519041793450418303401 3812639281345087813727551)
      ·
        refine ⟨5718958922017631720591327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812639281345087813727551 5718958922017631720591327)
        ·
          refine ⟨8578438383026447580886991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5718958922017631720591327 8578438383026447580886991)
          ·
            refine ⟨12867657574539671371330487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8578438383026447580886991 12867657574539671371330487)
            ·
              refine ⟨19301486361809507056995731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12867657574539671371330487 19301486361809507056995731)
              ·
                refine ⟨28952229542714260585493597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19301486361809507056995731 28952229542714260585493597)
                ·
                  refine ⟨10857086078517847719560099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28952229542714260585493597 10857086078517847719560099)
                  ·
                    refine ⟨16285629117776771579340149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10857086078517847719560099 16285629117776771579340149)
                    ·
                      refine ⟨1526777729791572335563139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16285629117776771579340149 1526777729791572335563139)
                      ·
                        rfl

theorem cell23_2973389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 1, 3, 1, 5].length) (baseStart_2973389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973389 prefixEnd_2973389 := by exact prefixLift 2973389
  have htrace : WordTrace (prefixWord ++ tailWord_2973389) baseStart_2973389 baseEnd_2973389 := by
    simpa [prefixWord, tailWord_2973389, baseEnd_2973389] using wordTrace_append hprefix tailTrace_2973389
  have hstable : (prefixWord ++ tailWord_2973389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973389).length < 2 ^ (prefixWord ++ tailWord_2973389).sum := by decide
  have hdescent : baseEnd_2973389 < baseStart_2973389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973409 : List Nat := [1, 2, 3, 1, 5, 2, 2, 7]
def baseStart_2973409 : Nat := 118140960795 + 2973409 * 2 ^ 59
def prefixEnd_2973409 : Nat := 4983230072969 + 3 ^ 40 * 2973409 * 2
def baseEnd_2973409 : Nat := 56547703681654157678261

theorem tailTrace_2973409 : CollatzResearch.WordTrace tailWord_2973409 prefixEnd_2973409 56547703681654157678261 := by
  unfold tailWord_2973409
  simp only [CollatzResearch.WordTrace]
  refine ⟨108449135684854485672867281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72299423789902990448578187 108449135684854485672867281)
  ·
    refine ⟨81336851763640864254650461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108449135684854485672867281 81336851763640864254650461)
    ·
      refine ⟨30501319411365324095493923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81336851763640864254650461 30501319411365324095493923)
      ·
        refine ⟨45751979117047986143240885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30501319411365324095493923 45751979117047986143240885)
        ·
          refine ⟨4289248042223248700928833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45751979117047986143240885 4289248042223248700928833)
          ·
            refine ⟨3216936031667436525696625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4289248042223248700928833 3216936031667436525696625)
            ·
              refine ⟨2412702023750577394272469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3216936031667436525696625 2412702023750577394272469)
              ·
                refine ⟨56547703681654157678261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2412702023750577394272469 56547703681654157678261)
                ·
                  rfl

theorem cell23_2973409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 7].length) (baseStart_2973409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973409 prefixEnd_2973409 := by exact prefixLift 2973409
  have htrace : WordTrace (prefixWord ++ tailWord_2973409) baseStart_2973409 baseEnd_2973409 := by
    simpa [prefixWord, tailWord_2973409, baseEnd_2973409] using wordTrace_append hprefix tailTrace_2973409
  have hstable : (prefixWord ++ tailWord_2973409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973409).length < 2 ^ (prefixWord ++ tailWord_2973409).sum := by decide
  have hdescent : baseEnd_2973409 < baseStart_2973409 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973435 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 2, 6]
def baseStart_2973435 : Nat := 118140960795 + 2973435 * 2 ^ 59
def prefixEnd_2973435 : Nat := 4983230072969 + 3 ^ 40 * 2973435 * 2
def baseEnd_2973435 : Nat := 508933783300559718529309

theorem tailTrace_2973435 : CollatzResearch.WordTrace tailWord_2973435 prefixEnd_2973435 508933783300559718529309 := by
  unfold tailWord_2973435
  simp only [CollatzResearch.WordTrace]
  refine ⟨108450083982760292113313759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72300055988506861408875839 108450083982760292113313759)
  ·
    refine ⟨162675125974140438169970639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108450083982760292113313759 162675125974140438169970639)
    ·
      refine ⟨244012688961210657254955959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162675125974140438169970639 244012688961210657254955959)
      ·
        refine ⟨366019033441815985882433939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244012688961210657254955959 366019033441815985882433939)
        ·
          refine ⟨549028550162723978823650909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366019033441815985882433939 549028550162723978823650909)
          ·
            refine ⟨205885706311021492058869091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549028550162723978823650909 205885706311021492058869091)
            ·
              refine ⟨308828559466532238088303637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205885706311021492058869091 308828559466532238088303637)
              ·
                refine ⟨14476338724993698660389233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 308828559466532238088303637 14476338724993698660389233)
                ·
                  refine ⟨10857254043745273995291925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14476338724993698660389233 10857254043745273995291925)
                  ·
                    refine ⟨508933783300559718529309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10857254043745273995291925 508933783300559718529309)
                    ·
                      rfl

theorem cell23_2973435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 6].length) (baseStart_2973435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973435 prefixEnd_2973435 := by exact prefixLift 2973435
  have htrace : WordTrace (prefixWord ++ tailWord_2973435) baseStart_2973435 baseEnd_2973435 := by
    simpa [prefixWord, tailWord_2973435, baseEnd_2973435] using wordTrace_append hprefix tailTrace_2973435
  have hstable : (prefixWord ++ tailWord_2973435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973435).length < 2 ^ (prefixWord ++ tailWord_2973435).sum := by decide
  have hdescent : baseEnd_2973435 < baseStart_2973435 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973459 : List Nat := [1, 1, 1, 2, 1, 3, 2, 2, 6, 2, 2]
def baseStart_2973459 : Nat := 118140960795 + 2973459 * 2 ^ 59
def prefixEnd_2973459 : Nat := 4983230072969 + 3 ^ 40 * 2973459 * 2
def baseEnd_2973459 : Nat := 1526813673437387061687817

theorem tailTrace_2973459 : CollatzResearch.WordTrace tailWord_2973459 prefixEnd_2973459 1526813673437387061687817 := by
  unfold tailWord_2973459
  simp only [CollatzResearch.WordTrace]
  refine ⟨108450959334673344212187431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72300639556448896141458287 108450959334673344212187431)
  ·
    refine ⟨162676439002010016318281147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108450959334673344212187431 162676439002010016318281147)
    ·
      refine ⟨244014658503015024477421721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162676439002010016318281147 244014658503015024477421721)
      ·
        refine ⟨183010993877261268358066291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244014658503015024477421721 183010993877261268358066291)
        ·
          refine ⟨274516490815891902537099437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183010993877261268358066291 274516490815891902537099437)
          ·
            refine ⟨102943684055959463451412289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 274516490815891902537099437 102943684055959463451412289)
            ·
              refine ⟨77207763041969597588559217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102943684055959463451412289 77207763041969597588559217)
              ·
                refine ⟨57905822281477198191419413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77207763041969597588559217 57905822281477198191419413)
                ·
                  refine ⟨2714335419444243665222785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 57905822281477198191419413 2714335419444243665222785)
                  ·
                    refine ⟨2035751564583182748917089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2714335419444243665222785 2035751564583182748917089)
                    ·
                      refine ⟨1526813673437387061687817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035751564583182748917089 1526813673437387061687817)
                      ·
                        rfl

theorem cell23_2973459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 2, 2, 6, 2, 2].length) (baseStart_2973459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973459 prefixEnd_2973459 := by exact prefixLift 2973459
  have htrace : WordTrace (prefixWord ++ tailWord_2973459) baseStart_2973459 baseEnd_2973459 := by
    simpa [prefixWord, tailWord_2973459, baseEnd_2973459] using wordTrace_append hprefix tailTrace_2973459
  have hstable : (prefixWord ++ tailWord_2973459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973459).length < 2 ^ (prefixWord ++ tailWord_2973459).sum := by decide
  have hdescent : baseEnd_2973459 < baseStart_2973459 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973463 : List Nat := [1, 1, 3, 4, 2, 3, 1, 2, 1, 3, 2]
def baseStart_2973463 : Nat := 118140960795 + 2973463 * 2 ^ 59
def prefixEnd_2973463 : Nat := 4983230072969 + 3 ^ 40 * 2973463 * 2
def baseEnd_2973463 : Nat := 1526815727360005046037799

theorem tailTrace_2973463 : CollatzResearch.WordTrace tailWord_2973463 prefixEnd_2973463 1526815727360005046037799 := by
  unfold tailWord_2973463
  simp only [CollatzResearch.WordTrace]
  refine ⟨108451105226658852895333043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72300736817772568596888695 108451105226658852895333043)
  ·
    refine ⟨162676657839988279342999565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108451105226658852895333043 162676657839988279342999565)
    ·
      refine ⟨61003746689995604753624837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162676657839988279342999565 61003746689995604753624837)
      ·
        refine ⟨11438202504374175891304657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61003746689995604753624837 11438202504374175891304657)
        ·
          refine ⟨8578651878280631918478493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11438202504374175891304657 8578651878280631918478493)
          ·
            refine ⟨3216994454355236969429435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8578651878280631918478493 3216994454355236969429435)
            ·
              refine ⟨4825491681532855454144153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3216994454355236969429435 4825491681532855454144153)
              ·
                refine ⟨3619118761149641590608115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4825491681532855454144153 3619118761149641590608115)
                ·
                  refine ⟨5428678141724462385912173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619118761149641590608115 5428678141724462385912173)
                  ·
                    refine ⟨2035754303146673394717065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5428678141724462385912173 2035754303146673394717065)
                    ·
                      refine ⟨1526815727360005046037799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035754303146673394717065 1526815727360005046037799)
                      ·
                        rfl

theorem cell23_2973463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 2, 3, 1, 2, 1, 3, 2].length) (baseStart_2973463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973463 prefixEnd_2973463 := by exact prefixLift 2973463
  have htrace : WordTrace (prefixWord ++ tailWord_2973463) baseStart_2973463 baseEnd_2973463 := by
    simpa [prefixWord, tailWord_2973463, baseEnd_2973463] using wordTrace_append hprefix tailTrace_2973463
  have hstable : (prefixWord ++ tailWord_2973463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973463).length < 2 ^ (prefixWord ++ tailWord_2973463).sum := by decide
  have hdescent : baseEnd_2973463 < baseStart_2973463 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973476 : List Nat := [2, 3, 1, 3, 2, 2, 1, 2, 1, 4, 2]
def baseStart_2973476 : Nat := 118140960795 + 2973476 * 2 ^ 59
def prefixEnd_2973476 : Nat := 4983230072969 + 3 ^ 40 * 2973476 * 2
def baseEnd_2973476 : Nat := 1526822402608513495175239

theorem tailTrace_2973476 : CollatzResearch.WordTrace tailWord_2973476 prefixEnd_2973476 1526822402608513495175239 := by
  unfold tailWord_2973476
  simp only [CollatzResearch.WordTrace]
  refine ⟨54225789687805878057778141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72301052917074504077037521 54225789687805878057778141)
  ·
    refine ⟨20334671132927204271666803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54225789687805878057778141 20334671132927204271666803)
    ·
      refine ⟨30502006699390806407500205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20334671132927204271666803 30502006699390806407500205)
      ·
        refine ⟨11438252512271552402812577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30502006699390806407500205 11438252512271552402812577)
        ·
          refine ⟨8578689384203664302109433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11438252512271552402812577 8578689384203664302109433)
          ·
            refine ⟨6434017038152748226582075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578689384203664302109433 6434017038152748226582075)
            ·
              refine ⟨9651025557229122339873113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6434017038152748226582075 9651025557229122339873113)
              ·
                refine ⟨7238269167921841754904835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9651025557229122339873113 7238269167921841754904835)
                ·
                  refine ⟨10857403751882762632357253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7238269167921841754904835 10857403751882762632357253)
                  ·
                    refine ⟨2035763203478017993566985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10857403751882762632357253 2035763203478017993566985)
                    ·
                      refine ⟨1526822402608513495175239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035763203478017993566985 1526822402608513495175239)
                      ·
                        rfl

theorem cell23_2973476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 2, 1, 2, 1, 4, 2].length) (baseStart_2973476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973476 prefixEnd_2973476 := by exact prefixLift 2973476
  have htrace : WordTrace (prefixWord ++ tailWord_2973476) baseStart_2973476 baseEnd_2973476 := by
    simpa [prefixWord, tailWord_2973476, baseEnd_2973476] using wordTrace_append hprefix tailTrace_2973476
  have hstable : (prefixWord ++ tailWord_2973476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973476).length < 2 ^ (prefixWord ++ tailWord_2973476).sum := by decide
  have hdescent : baseEnd_2973476 < baseStart_2973476 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973510 : List Nat := [6, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2]
def baseStart_2973510 : Nat := 118140960795 + 2973510 * 2 ^ 59
def prefixEnd_2973510 : Nat := 4983230072969 + 3 ^ 40 * 2973510 * 2
def baseEnd_2973510 : Nat := 1526839860950766362150083

theorem tailTrace_2973510 : CollatzResearch.WordTrace tailWord_2973510 prefixEnd_2973510 1526839860950766362150083 := by
  unfold tailWord_2973510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3389150608046518122571687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72301879638325719948195989 3389150608046518122571687)
  ·
    refine ⟨5083725912069777183857531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3389150608046518122571687 5083725912069777183857531)
    ·
      refine ⟨7625588868104665775786297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5083725912069777183857531 7625588868104665775786297)
      ·
        refine ⟨5719191651078499331839723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625588868104665775786297 5719191651078499331839723)
        ·
          refine ⟨8578787476617748997759585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719191651078499331839723 8578787476617748997759585)
          ·
            refine ⟨6434090607463311748319689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8578787476617748997759585 6434090607463311748319689)
            ·
              refine ⟨4825567955597483811239767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6434090607463311748319689 4825567955597483811239767)
              ·
                refine ⟨7238351933396225716859651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4825567955597483811239767 7238351933396225716859651)
                ·
                  refine ⟨10857527900094338575289477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7238351933396225716859651 10857527900094338575289477)
                  ·
                    refine ⟨2035786481267688482866777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10857527900094338575289477 2035786481267688482866777)
                    ·
                      refine ⟨1526839860950766362150083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035786481267688482866777 1526839860950766362150083)
                      ·
                        rfl

theorem cell23_2973510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 1, 4, 2].length) (baseStart_2973510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973510 prefixEnd_2973510 := by exact prefixLift 2973510
  have htrace : WordTrace (prefixWord ++ tailWord_2973510) baseStart_2973510 baseEnd_2973510 := by
    simpa [prefixWord, tailWord_2973510, baseEnd_2973510] using wordTrace_append hprefix tailTrace_2973510
  have hstable : (prefixWord ++ tailWord_2973510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973510).length < 2 ^ (prefixWord ++ tailWord_2973510).sum := by decide
  have hdescent : baseEnd_2973510 < baseStart_2973510 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973549 : List Nat := [1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_2973549 : Nat := 118140960795 + 2973549 * 2 ^ 59
def prefixEnd_2973549 : Nat := 4983230072969 + 3 ^ 40 * 2973549 * 2
def baseEnd_2973549 : Nat := 1526859886696291709562403

theorem tailTrace_2973549 : CollatzResearch.WordTrace tailWord_2973549 prefixEnd_2973549 1526859886696291709562403 := by
  unfold tailWord_2973549
  simp only [CollatzResearch.WordTrace]
  refine ⟨108454241904347289582963701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72302827936231526388642467 108454241904347289582963701)
  ·
    refine ⟨10167585178532558398402847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 108454241904347289582963701 10167585178532558398402847)
    ·
      refine ⟨15251377767798837597604271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10167585178532558398402847 15251377767798837597604271)
      ·
        refine ⟨22877066651698256396406407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15251377767798837597604271 22877066651698256396406407)
        ·
          refine ⟨34315599977547384594609611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22877066651698256396406407 34315599977547384594609611)
          ·
            refine ⟨51473399966321076891914417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34315599977547384594609611 51473399966321076891914417)
            ·
              refine ⟨38605049974740807668935813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51473399966321076891914417 38605049974740807668935813)
              ·
                refine ⟨7238446870263901437925465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38605049974740807668935813 7238446870263901437925465)
                ·
                  refine ⟨5428835152697926078444099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7238446870263901437925465 5428835152697926078444099)
                  ·
                    refine ⟨8143252729046889117666149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5428835152697926078444099 8143252729046889117666149)
                    ·
                      refine ⟨1526859886696291709562403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8143252729046889117666149 1526859886696291709562403)
                      ·
                        rfl

theorem cell23_2973549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_2973549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973549 prefixEnd_2973549 := by exact prefixLift 2973549
  have htrace : WordTrace (prefixWord ++ tailWord_2973549) baseStart_2973549 baseEnd_2973549 := by
    simpa [prefixWord, tailWord_2973549, baseEnd_2973549] using wordTrace_append hprefix tailTrace_2973549
  have hstable : (prefixWord ++ tailWord_2973549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973549).length < 2 ^ (prefixWord ++ tailWord_2973549).sum := by decide
  have hdescent : baseEnd_2973549 < baseStart_2973549 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973566 : List Nat := [4, 2, 3, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_2973566 : Nat := 118140960795 + 2973566 * 2 ^ 59
def prefixEnd_2973566 : Nat := 4983230072969 + 3 ^ 40 * 2973566 * 2
def baseEnd_2973566 : Nat := 1526868615867418143049825

theorem tailTrace_2973566 : CollatzResearch.WordTrace tailWord_2973566 prefixEnd_2973566 1526868615867418143049825 := by
  unfold tailWord_2973566
  simp only [CollatzResearch.WordTrace]
  refine ⟨13556857743160712685791569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72303241296857134324221701 13556857743160712685791569)
  ·
    refine ⟨10167643307370534514343677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13556857743160712685791569 10167643307370534514343677)
    ·
      refine ⟨3812866240263950442878879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10167643307370534514343677 3812866240263950442878879)
      ·
        refine ⟨5719299360395925664318319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3812866240263950442878879 5719299360395925664318319)
        ·
          refine ⟨8578949040593888496477479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719299360395925664318319 8578949040593888496477479)
          ·
            refine ⟨12868423560890832744716219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8578949040593888496477479 12868423560890832744716219)
            ·
              refine ⟨19302635341336249117074329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12868423560890832744716219 19302635341336249117074329)
              ·
                refine ⟨14476976506002186837805747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19302635341336249117074329 14476976506002186837805747)
                ·
                  refine ⟨21715464759003280256708621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14476976506002186837805747 21715464759003280256708621)
                  ·
                    refine ⟨8143299284626230096265733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21715464759003280256708621 8143299284626230096265733)
                    ·
                      refine ⟨1526868615867418143049825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8143299284626230096265733 1526868615867418143049825)
                      ·
                        rfl

theorem cell23_2973566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_2973566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973566 prefixEnd_2973566 := by exact prefixLift 2973566
  have htrace : WordTrace (prefixWord ++ tailWord_2973566) baseStart_2973566 baseEnd_2973566 := by
    simpa [prefixWord, tailWord_2973566, baseEnd_2973566] using wordTrace_append hprefix tailTrace_2973566
  have hstable : (prefixWord ++ tailWord_2973566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973566).length < 2 ^ (prefixWord ++ tailWord_2973566).sum := by decide
  have hdescent : baseEnd_2973566 < baseStart_2973566 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973586 : List Nat := [3, 2, 3, 2, 1, 1, 2, 1, 1, 4, 3]
def baseStart_2973586 : Nat := 118140960795 + 2973586 * 2 ^ 59
def prefixEnd_2973586 : Nat := 4983230072969 + 3 ^ 40 * 2973586 * 2
def baseEnd_2973586 : Nat := 1526878885480508064799733

theorem tailTrace_2973586 : CollatzResearch.WordTrace tailWord_2973586 prefixEnd_2973586 1526878885480508064799733 := by
  unfold tailWord_2973586
  simp only [CollatzResearch.WordTrace]
  refine ⟨27113897851303311225515153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72303727603475496601373741 27113897851303311225515153)
  ·
    refine ⟨20335423388477483419136365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27113897851303311225515153 20335423388477483419136365)
    ·
      refine ⟨7625783770679056282176137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20335423388477483419136365 7625783770679056282176137)
      ·
        refine ⟨5719337828009292211632103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7625783770679056282176137 5719337828009292211632103)
        ·
          refine ⟨8579006742013938317448155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5719337828009292211632103 8579006742013938317448155)
          ·
            refine ⟨12868510113020907476172233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8579006742013938317448155 12868510113020907476172233)
            ·
              refine ⟨9651382584765680607129175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12868510113020907476172233 9651382584765680607129175)
              ·
                refine ⟨14477073877148520910693763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9651382584765680607129175 14477073877148520910693763)
                ·
                  refine ⟨21715610815722781366040645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14477073877148520910693763 21715610815722781366040645)
                  ·
                    refine ⟨4071677027948021506132621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21715610815722781366040645 4071677027948021506132621)
                    ·
                      refine ⟨1526878885480508064799733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4071677027948021506132621 1526878885480508064799733)
                      ·
                        rfl

theorem cell23_2973586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 1, 1, 4, 3].length) (baseStart_2973586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973586 prefixEnd_2973586 := by exact prefixLift 2973586
  have htrace : WordTrace (prefixWord ++ tailWord_2973586) baseStart_2973586 baseEnd_2973586 := by
    simpa [prefixWord, tailWord_2973586, baseEnd_2973586] using wordTrace_append hprefix tailTrace_2973586
  have hstable : (prefixWord ++ tailWord_2973586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973586).length < 2 ^ (prefixWord ++ tailWord_2973586).sum := by decide
  have hdescent : baseEnd_2973586 < baseStart_2973586 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973609 : List Nat := [1, 2, 1, 1, 1, 1, 4, 2, 3, 5, 2]
def baseStart_2973609 : Nat := 118140960795 + 2973609 * 2 ^ 59
def prefixEnd_2973609 : Nat := 4983230072969 + 3 ^ 40 * 2973609 * 2
def baseEnd_2973609 : Nat := 1526890695535561474812127

theorem tailTrace_2973609 : CollatzResearch.WordTrace tailWord_2973609 prefixEnd_2973609 1526890695535561474812127 := by
  unfold tailWord_2973609
  simp only [CollatzResearch.WordTrace]
  refine ⟨108456430284129919830147881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72304286856086613220098587 108456430284129919830147881)
  ·
    refine ⟨81342322713097439872610911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108456430284129919830147881 81342322713097439872610911)
    ·
      refine ⟨122013484069646159808916367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81342322713097439872610911 122013484069646159808916367)
      ·
        refine ⟨183020226104469239713374551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122013484069646159808916367 183020226104469239713374551)
        ·
          refine ⟨274530339156703859570061827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183020226104469239713374551 274530339156703859570061827)
          ·
            refine ⟨411795508735055789355092741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274530339156703859570061827 411795508735055789355092741)
            ·
              refine ⟨77211657887822960504079889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 411795508735055789355092741 77211657887822960504079889)
              ·
                refine ⟨57908743415867220378059917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77211657887822960504079889 57908743415867220378059917)
                ·
                  refine ⟨21715778780950207641772469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57908743415867220378059917 21715778780950207641772469)
                  ·
                    refine ⟨2035854260714081966416169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21715778780950207641772469 2035854260714081966416169)
                    ·
                      refine ⟨1526890695535561474812127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035854260714081966416169 1526890695535561474812127)
                      ·
                        rfl

theorem cell23_2973609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 2, 3, 5, 2].length) (baseStart_2973609 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973609 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973609 prefixEnd_2973609 := by exact prefixLift 2973609
  have htrace : WordTrace (prefixWord ++ tailWord_2973609) baseStart_2973609 baseEnd_2973609 := by
    simpa [prefixWord, tailWord_2973609, baseEnd_2973609] using wordTrace_append hprefix tailTrace_2973609
  have hstable : (prefixWord ++ tailWord_2973609).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973609).length < 2 ^ (prefixWord ++ tailWord_2973609).sum := by decide
  have hdescent : baseEnd_2973609 < baseStart_2973609 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973649 : List Nat := [1, 2, 2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_2973649 : Nat := 118140960795 + 2973649 * 2 ^ 59
def prefixEnd_2973649 : Nat := 4983230072969 + 3 ^ 40 * 2973649 * 2
def baseEnd_2973649 : Nat := 508970411587247106103981

theorem tailTrace_2973649 : CollatzResearch.WordTrace tailWord_2973649 prefixEnd_2973649 508970411587247106103981 := by
  unfold tailWord_2973649
  simp only [CollatzResearch.WordTrace]
  refine ⟨108457889203985006661604001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72305259469323337774402667 108457889203985006661604001)
  ·
    refine ⟨81343416902988754996203001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108457889203985006661604001 81343416902988754996203001)
    ·
      refine ⟨61007562677241566247152251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81343416902988754996203001 61007562677241566247152251)
      ·
        refine ⟨91511344015862349370728377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61007562677241566247152251 91511344015862349370728377)
        ·
          refine ⟨68633508011896762028046283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91511344015862349370728377 68633508011896762028046283)
          ·
            refine ⟨102950262017845143042069425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68633508011896762028046283 102950262017845143042069425)
            ·
              refine ⟨77212696513383857281552069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102950262017845143042069425 77212696513383857281552069)
              ·
                refine ⟨14477380596259473240291013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 77212696513383857281552069 14477380596259473240291013)
                ·
                  refine ⟨2714508861798651232554565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14477380596259473240291013 2714508861798651232554565)
                  ·
                    refine ⟨508970411587247106103981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714508861798651232554565 508970411587247106103981)
                    ·
                      rfl

theorem cell23_2973649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_2973649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973649 prefixEnd_2973649 := by exact prefixLift 2973649
  have htrace : WordTrace (prefixWord ++ tailWord_2973649) baseStart_2973649 baseEnd_2973649 := by
    simpa [prefixWord, tailWord_2973649, baseEnd_2973649] using wordTrace_append hprefix tailTrace_2973649
  have hstable : (prefixWord ++ tailWord_2973649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973649).length < 2 ^ (prefixWord ++ tailWord_2973649).sum := by decide
  have hdescent : baseEnd_2973649 < baseStart_2973649 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973653 : List Nat := [1, 3, 2, 3, 2, 2, 3, 1, 1, 5]
def baseStart_2973653 : Nat := 118140960795 + 2973653 * 2 ^ 59
def prefixEnd_2973653 : Nat := 4983230072969 + 3 ^ 40 * 2973653 * 2
def baseEnd_2973653 : Nat := 508971096228119767553975

theorem tailTrace_2973653 : CollatzResearch.WordTrace tailWord_2973653 prefixEnd_2973653 508971096228119767553975 := by
  unfold tailWord_2973653
  simp only [CollatzResearch.WordTrace]
  refine ⟨108458035095970515344749613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72305356730647010229833075 108458035095970515344749613)
  ·
    refine ⟨40671763160988943254281105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108458035095970515344749613 40671763160988943254281105)
    ·
      refine ⟨30503822370741707440710829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40671763160988943254281105 30503822370741707440710829)
      ·
        refine ⟨11438933389028140290266561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30503822370741707440710829 11438933389028140290266561)
        ·
          refine ⟨8579200041771105217699921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11438933389028140290266561 8579200041771105217699921)
          ·
            refine ⟨6434400031328328913274941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8579200041771105217699921 6434400031328328913274941)
            ·
              refine ⟨2412900011748123342478103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6434400031328328913274941 2412900011748123342478103)
              ·
                refine ⟨3619350017622185013717155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2412900011748123342478103 3619350017622185013717155)
                ·
                  refine ⟨5429025026433277520575733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619350017622185013717155 5429025026433277520575733)
                  ·
                    refine ⟨508971096228119767553975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5429025026433277520575733 508971096228119767553975)
                    ·
                      rfl

theorem cell23_2973653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 3, 1, 1, 5].length) (baseStart_2973653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973653 prefixEnd_2973653 := by exact prefixLift 2973653
  have htrace : WordTrace (prefixWord ++ tailWord_2973653) baseStart_2973653 baseEnd_2973653 := by
    simpa [prefixWord, tailWord_2973653, baseEnd_2973653] using wordTrace_append hprefix tailTrace_2973653
  have hstable : (prefixWord ++ tailWord_2973653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973653).length < 2 ^ (prefixWord ++ tailWord_2973653).sum := by decide
  have hdescent : baseEnd_2973653 < baseStart_2973653 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973667 : List Nat := [1, 1, 1, 6, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2973667 : Nat := 118140960795 + 2973667 * 2 ^ 59
def prefixEnd_2973667 : Nat := 4983230072969 + 3 ^ 40 * 2973667 * 2
def baseEnd_2973667 : Nat := 1526920477413522247886861

theorem tailTrace_2973667 : CollatzResearch.WordTrace tailWord_2973667 prefixEnd_2973667 1526920477413522247886861 := by
  unfold tailWord_2973667
  simp only [CollatzResearch.WordTrace]
  refine ⟨108458545717919795735759255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72305697145279863823839503 108458545717919795735759255)
  ·
    refine ⟨162687818576879693603638883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108458545717919795735759255 162687818576879693603638883)
    ·
      refine ⟨244031727865319540405458325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162687818576879693603638883 244031727865319540405458325)
      ·
        refine ⟨11438987243686853456505859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244031727865319540405458325 11438987243686853456505859)
        ·
          refine ⟨17158480865530280184758789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11438987243686853456505859 17158480865530280184758789)
          ·
            refine ⟨3217215162286927534642273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17158480865530280184758789 3217215162286927534642273)
            ·
              refine ⟨2412911371715195650981705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3217215162286927534642273 2412911371715195650981705)
              ·
                refine ⟨1809683528786396738236279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2412911371715195650981705 1809683528786396738236279)
                ·
                  refine ⟨2714525293179595107354419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809683528786396738236279 2714525293179595107354419)
                  ·
                    refine ⟨4071787939769392661031629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2714525293179595107354419 4071787939769392661031629)
                    ·
                      refine ⟨1526920477413522247886861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4071787939769392661031629 1526920477413522247886861)
                      ·
                        rfl

theorem cell23_2973667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2973667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973667 prefixEnd_2973667 := by exact prefixLift 2973667
  have htrace : WordTrace (prefixWord ++ tailWord_2973667) baseStart_2973667 baseEnd_2973667 := by
    simpa [prefixWord, tailWord_2973667, baseEnd_2973667] using wordTrace_append hprefix tailTrace_2973667
  have hstable : (prefixWord ++ tailWord_2973667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973667).length < 2 ^ (prefixWord ++ tailWord_2973667).sum := by decide
  have hdescent : baseEnd_2973667 < baseStart_2973667 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973759 : List Nat := [1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4]
def baseStart_2973759 : Nat := 118140960795 + 2973759 * 2 ^ 59
def prefixEnd_2973759 : Nat := 4983230072969 + 3 ^ 40 * 2973759 * 2
def baseEnd_2973759 : Nat := 1526967717633735887936437

theorem tailTrace_2973759 : CollatzResearch.WordTrace tailWord_2973759 prefixEnd_2973759 1526967717633735887936437 := by
  unfold tailWord_2973759
  simp only [CollatzResearch.WordTrace]
  refine ⟨108461901233586495448108331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72307934155724330298738887 108461901233586495448108331)
  ·
    refine ⟨162692851850379743172162497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108461901233586495448108331 162692851850379743172162497)
    ·
      refine ⟨122019638887784807379121873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162692851850379743172162497 122019638887784807379121873)
      ·
        refine ⟨91514729165838605534341405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122019638887784807379121873 91514729165838605534341405)
        ·
          refine ⟨34318023437189477075378027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91514729165838605534341405 34318023437189477075378027)
          ·
            refine ⟨51477035155784215613067041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34318023437189477075378027 51477035155784215613067041)
            ·
              refine ⟨38607776366838161709800281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51477035155784215613067041 38607776366838161709800281)
              ·
                refine ⟨28955832275128621282350211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38607776366838161709800281 28955832275128621282350211)
                ·
                  refine ⟨43433748412692931923525317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28955832275128621282350211 43433748412692931923525317)
                  ·
                    refine ⟨8143827827379924735660997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43433748412692931923525317 8143827827379924735660997)
                    ·
                      refine ⟨1526967717633735887936437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8143827827379924735660997 1526967717633735887936437)
                      ·
                        rfl

theorem cell23_2973759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 2, 1, 4, 4].length) (baseStart_2973759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973759 prefixEnd_2973759 := by exact prefixLift 2973759
  have htrace : WordTrace (prefixWord ++ tailWord_2973759) baseStart_2973759 baseEnd_2973759 := by
    simpa [prefixWord, tailWord_2973759, baseEnd_2973759] using wordTrace_append hprefix tailTrace_2973759
  have hstable : (prefixWord ++ tailWord_2973759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973759).length < 2 ^ (prefixWord ++ tailWord_2973759).sum := by decide
  have hdescent : baseEnd_2973759 < baseStart_2973759 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973780 : List Nat := [2, 4, 1, 1, 1, 1, 1, 6, 2, 2, 2]
def baseStart_2973780 : Nat := 118140960795 + 2973780 * 2 ^ 59
def prefixEnd_2973780 : Nat := 4983230072969 + 3 ^ 40 * 2973780 * 2
def baseEnd_2973780 : Nat := 1526978500727480305773841

theorem tailTrace_2973780 : CollatzResearch.WordTrace tailWord_2973780 prefixEnd_2973780 1526978500727480305773841 := by
  unfold tailWord_2973780
  simp only [CollatzResearch.WordTrace]
  refine ⟨54231333583255208017311397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72308444777673610689748529 54231333583255208017311397)
  ·
    refine ⟨10168375046860351503245887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 54231333583255208017311397 10168375046860351503245887)
    ·
      refine ⟨15252562570290527254868831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10168375046860351503245887 15252562570290527254868831)
      ·
        refine ⟨22878843855435790882303247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15252562570290527254868831 22878843855435790882303247)
        ·
          refine ⟨34318265783153686323454871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22878843855435790882303247 34318265783153686323454871)
          ·
            refine ⟨51477398674730529485182307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34318265783153686323454871 51477398674730529485182307)
            ·
              refine ⟨77216098012095794227773461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51477398674730529485182307 77216098012095794227773461)
              ·
                refine ⟨3619504594316990354426881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77216098012095794227773461 3619504594316990354426881)
                ·
                  refine ⟨2714628445737742765820161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3619504594316990354426881 2714628445737742765820161)
                  ·
                    refine ⟨2035971334303307074365121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2714628445737742765820161 2035971334303307074365121)
                    ·
                      refine ⟨1526978500727480305773841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035971334303307074365121 1526978500727480305773841)
                      ·
                        rfl

theorem cell23_2973780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 6, 2, 2, 2].length) (baseStart_2973780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973780 prefixEnd_2973780 := by exact prefixLift 2973780
  have htrace : WordTrace (prefixWord ++ tailWord_2973780) baseStart_2973780 baseEnd_2973780 := by
    simpa [prefixWord, tailWord_2973780, baseEnd_2973780] using wordTrace_append hprefix tailTrace_2973780
  have hstable : (prefixWord ++ tailWord_2973780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973780).length < 2 ^ (prefixWord ++ tailWord_2973780).sum := by decide
  have hdescent : baseEnd_2973780 < baseStart_2973780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973796 : List Nat := [2, 3, 1, 1, 2, 1, 2, 3, 2, 3, 3]
def baseStart_2973796 : Nat := 118140960795 + 2973796 * 2 ^ 59
def prefixEnd_2973796 : Nat := 4983230072969 + 3 ^ 40 * 2973796 * 2
def baseEnd_2973796 : Nat := 1526986716417952243173767

theorem tailTrace_2973796 : CollatzResearch.WordTrace tailWord_2973796 prefixEnd_2973796 1526986716417952243173767 := by
  unfold tailWord_2973796
  simp only [CollatzResearch.WordTrace]
  refine ⟨54231625367226225383602621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72308833822968300511470161 54231625367226225383602621)
  ·
    refine ⟨20336859512709834518850983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54231625367226225383602621 20336859512709834518850983)
    ·
      refine ⟨30505289269064751778276475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20336859512709834518850983 30505289269064751778276475)
      ·
        refine ⟨45757933903597127667414713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30505289269064751778276475 45757933903597127667414713)
        ·
          refine ⟨34318450427697845750561035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45757933903597127667414713 34318450427697845750561035)
          ·
            refine ⟨51477675641546768625841553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34318450427697845750561035 51477675641546768625841553)
            ·
              refine ⟨38608256731160076469381165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51477675641546768625841553 38608256731160076469381165)
              ·
                refine ⟨14478096274185028676017937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38608256731160076469381165 14478096274185028676017937)
                ·
                  refine ⟨10858572205638771507013453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14478096274185028676017937 10858572205638771507013453)
                  ·
                    refine ⟨4071964577114539315130045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10858572205638771507013453 4071964577114539315130045)
                    ·
                      refine ⟨1526986716417952243173767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4071964577114539315130045 1526986716417952243173767)
                      ·
                        rfl

theorem cell23_2973796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 2, 3, 2, 3, 3].length) (baseStart_2973796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973796 prefixEnd_2973796 := by exact prefixLift 2973796
  have htrace : WordTrace (prefixWord ++ tailWord_2973796) baseStart_2973796 baseEnd_2973796 := by
    simpa [prefixWord, tailWord_2973796, baseEnd_2973796] using wordTrace_append hprefix tailTrace_2973796
  have hstable : (prefixWord ++ tailWord_2973796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973796).length < 2 ^ (prefixWord ++ tailWord_2973796).sum := by decide
  have hdescent : baseEnd_2973796 < baseStart_2973796 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973797 : List Nat := [1, 3, 1, 3, 2, 2, 4, 1, 2, 2, 2]
def baseStart_2973797 : Nat := 118140960795 + 2973797 * 2 ^ 59
def prefixEnd_2973797 : Nat := 4983230072969 + 3 ^ 40 * 2973797 * 2
def baseEnd_2973797 : Nat := 1526987229898606739261263

theorem tailTrace_2973797 : CollatzResearch.WordTrace tailWord_2973797 prefixEnd_2973797 1526987229898606739261263 := by
  unfold tailWord_2973797
  simp only [CollatzResearch.WordTrace]
  refine ⟨108463287207448827937991645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72308858138299218625327763 108463287207448827937991645)
  ·
    refine ⟨40673732702793310476746867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108463287207448827937991645 40673732702793310476746867)
    ·
      refine ⟨61010599054189965715120301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40673732702793310476746867 61010599054189965715120301)
      ·
        refine ⟨22878974645321237143170113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61010599054189965715120301 22878974645321237143170113)
        ·
          refine ⟨17159230983990927857377585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22878974645321237143170113 17159230983990927857377585)
          ·
            refine ⟨12869423237993195893033189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17159230983990927857377585 12869423237993195893033189)
            ·
              refine ⟨2413016857123724229943723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12869423237993195893033189 2413016857123724229943723)
              ·
                refine ⟨3619525285685586344915585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413016857123724229943723 3619525285685586344915585)
                ·
                  refine ⟨2714643964264189758686689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3619525285685586344915585 2714643964264189758686689)
                  ·
                    refine ⟨2035982973198142319015017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2714643964264189758686689 2035982973198142319015017)
                    ·
                      refine ⟨1526987229898606739261263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2035982973198142319015017 1526987229898606739261263)
                      ·
                        rfl

theorem cell23_2973797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_2973797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973797 prefixEnd_2973797 := by exact prefixLift 2973797
  have htrace : WordTrace (prefixWord ++ tailWord_2973797) baseStart_2973797 baseEnd_2973797 := by
    simpa [prefixWord, tailWord_2973797, baseEnd_2973797] using wordTrace_append hprefix tailTrace_2973797
  have hstable : (prefixWord ++ tailWord_2973797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973797).length < 2 ^ (prefixWord ++ tailWord_2973797).sum := by decide
  have hdescent : baseEnd_2973797 < baseStart_2973797 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973809 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 7]
def baseStart_2973809 : Nat := 118140960795 + 2973809 * 2 ^ 59
def prefixEnd_2973809 : Nat := 4983230072969 + 3 ^ 40 * 2973809 * 2
def baseEnd_2973809 : Nat := 1526993391666460692311207

theorem tailTrace_2973809 : CollatzResearch.WordTrace tailWord_2973809 prefixEnd_2973809 1526993391666460692311207 := by
  unfold tailWord_2973809
  simp only [CollatzResearch.WordTrace]
  refine ⟨108463724883405353987428481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72309149922270235991618987 108463724883405353987428481)
  ·
    refine ⟨81347793662554015490571361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108463724883405353987428481 81347793662554015490571361)
    ·
      refine ⟨61010845246915511617928521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81347793662554015490571361 61010845246915511617928521)
      ·
        refine ⟨45758133935186633713446391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61010845246915511617928521 45758133935186633713446391)
        ·
          refine ⟨68637200902779950570169587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45758133935186633713446391 68637200902779950570169587)
          ·
            refine ⟨102955801354169925855254381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68637200902779950570169587 102955801354169925855254381)
            ·
              refine ⟨38608425507813722195720393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 102955801354169925855254381 38608425507813722195720393)
              ·
                refine ⟨28956319130860291646790295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38608425507813722195720393 28956319130860291646790295)
                ·
                  refine ⟨43434478696290437470185443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28956319130860291646790295 43434478696290437470185443)
                  ·
                    refine ⟨65151718044435656205278165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 43434478696290437470185443 65151718044435656205278165)
                    ·
                      refine ⟨1526993391666460692311207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 65151718044435656205278165 1526993391666460692311207)
                      ·
                        rfl

theorem cell23_2973809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 1, 7].length) (baseStart_2973809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973809 prefixEnd_2973809 := by exact prefixLift 2973809
  have htrace : WordTrace (prefixWord ++ tailWord_2973809) baseStart_2973809 baseEnd_2973809 := by
    simpa [prefixWord, tailWord_2973809, baseEnd_2973809] using wordTrace_append hprefix tailTrace_2973809
  have hstable : (prefixWord ++ tailWord_2973809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973809).length < 2 ^ (prefixWord ++ tailWord_2973809).sum := by decide
  have hdescent : baseEnd_2973809 < baseStart_2973809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973853 : List Nat := [1, 4, 2, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_2973853 : Nat := 118140960795 + 2973853 * 2 ^ 59
def prefixEnd_2973853 : Nat := 4983230072969 + 3 ^ 40 * 2973853 * 2
def baseEnd_2973853 : Nat := 1527015984815258520161005

theorem tailTrace_2973853 : CollatzResearch.WordTrace tailWord_2973853 prefixEnd_2973853 1527015984815258520161005 := by
  unfold tailWord_2973853
  simp only [CollatzResearch.WordTrace]
  refine ⟨108465329695245949502030213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72310219796830633001353475 108465329695245949502030213)
  ·
    refine ⟨20337249317858615531630665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 108465329695245949502030213 20337249317858615531630665)
    ·
      refine ⟨15252936988393961648722999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20337249317858615531630665 15252936988393961648722999)
      ·
        refine ⟨22879405482590942473084499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15252936988393961648722999 22879405482590942473084499)
        ·
          refine ⟨34319108223886413709626749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22879405482590942473084499 34319108223886413709626749)
          ·
            refine ⟨12869665583957405141110031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34319108223886413709626749 12869665583957405141110031)
            ·
              refine ⟨19304498375936107711665047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12869665583957405141110031 19304498375936107711665047)
              ·
                refine ⟨28956747563904161567497571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19304498375936107711665047 28956747563904161567497571)
                ·
                  refine ⟨43435121345856242351246357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28956747563904161567497571 43435121345856242351246357)
                  ·
                    refine ⟨2036021313087011360214673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 43435121345856242351246357 2036021313087011360214673)
                    ·
                      refine ⟨1527015984815258520161005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036021313087011360214673 1527015984815258520161005)
                      ·
                        rfl

theorem cell23_2973853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_2973853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973853 prefixEnd_2973853 := by exact prefixLift 2973853
  have htrace : WordTrace (prefixWord ++ tailWord_2973853) baseStart_2973853 baseEnd_2973853 := by
    simpa [prefixWord, tailWord_2973853, baseEnd_2973853] using wordTrace_append hprefix tailTrace_2973853
  have hstable : (prefixWord ++ tailWord_2973853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973853).length < 2 ^ (prefixWord ++ tailWord_2973853).sum := by decide
  have hdescent : baseEnd_2973853 < baseStart_2973853 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973859 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 12]
def baseStart_2973859 : Nat := 118140960795 + 2973859 * 2 ^ 59
def prefixEnd_2973859 : Nat := 4983230072969 + 3 ^ 40 * 2973859 * 2
def baseEnd_2973859 : Nat := 169668785077687277409553

theorem tailTrace_2973859 : CollatzResearch.WordTrace tailWord_2973859 prefixEnd_2973859 169668785077687277409553 := by
  unfold tailWord_2973859
  simp only [CollatzResearch.WordTrace]
  refine ⟨108465548533224212526748631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72310365688816141684499087 108465548533224212526748631)
  ·
    refine ⟨162698322799836318790122947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108465548533224212526748631 162698322799836318790122947)
    ·
      refine ⟨244047484199754478185184421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162698322799836318790122947 244047484199754478185184421)
      ·
        refine ⟨45758903287453964659722079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 244047484199754478185184421 45758903287453964659722079)
        ·
          refine ⟨68638354931180946989583119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45758903287453964659722079 68638354931180946989583119)
          ·
            refine ⟨102957532396771420484374679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68638354931180946989583119 102957532396771420484374679)
            ·
              refine ⟨154436298595157130726562019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102957532396771420484374679 154436298595157130726562019)
              ·
                refine ⟨231654447892735696089843029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154436298595157130726562019 231654447892735696089843029)
                ·
                  refine ⟨169668785077687277409553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 231654447892735696089843029 169668785077687277409553)
                  ·
                    rfl

theorem cell23_2973859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 12].length) (baseStart_2973859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973859 prefixEnd_2973859 := by exact prefixLift 2973859
  have htrace : WordTrace (prefixWord ++ tailWord_2973859) baseStart_2973859 baseEnd_2973859 := by
    simpa [prefixWord, tailWord_2973859, baseEnd_2973859] using wordTrace_append hprefix tailTrace_2973859
  have hstable : (prefixWord ++ tailWord_2973859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973859).length < 2 ^ (prefixWord ++ tailWord_2973859).sum := by decide
  have hdescent : baseEnd_2973859 < baseStart_2973859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973880 : List Nat := [2, 1, 2, 1, 2, 1, 6, 3, 1, 4]
def baseStart_2973880 : Nat := 118140960795 + 2973880 * 2 ^ 59
def prefixEnd_2973880 : Nat := 4983230072969 + 3 ^ 40 * 2973880 * 2
def baseEnd_2973880 : Nat := 509009949597643304841127

theorem tailTrace_2973880 : CollatzResearch.WordTrace tailWord_2973880 prefixEnd_2973880 509009949597643304841127 := by
  unfold tailWord_2973880
  simp only [CollatzResearch.WordTrace]
  refine ⟨54233157233074066556631547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72310876310765422075508729 54233157233074066556631547)
  ·
    refine ⟨81349735849611099834947321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54233157233074066556631547 81349735849611099834947321)
    ·
      refine ⟨61012301887208324876210491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81349735849611099834947321 61012301887208324876210491)
      ·
        refine ⟨91518452830812487314315737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61012301887208324876210491 91518452830812487314315737)
        ·
          refine ⟨68638839623109365485736803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91518452830812487314315737 68638839623109365485736803)
          ·
            refine ⟨102958259434664048228605205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68638839623109365485736803 102958259434664048228605205)
            ·
              refine ⟨4826168410999877260715869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 102958259434664048228605205 4826168410999877260715869)
              ·
                refine ⟨1809813154124953972768451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826168410999877260715869 1809813154124953972768451)
                ·
                  refine ⟨2714719731187430959152677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809813154124953972768451 2714719731187430959152677)
                  ·
                    refine ⟨509009949597643304841127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714719731187430959152677 509009949597643304841127)
                    ·
                      rfl

theorem cell23_2973880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 6, 3, 1, 4].length) (baseStart_2973880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973880 prefixEnd_2973880 := by exact prefixLift 2973880
  have htrace : WordTrace (prefixWord ++ tailWord_2973880) baseStart_2973880 baseEnd_2973880 := by
    simpa [prefixWord, tailWord_2973880, baseEnd_2973880] using wordTrace_append hprefix tailTrace_2973880
  have hstable : (prefixWord ++ tailWord_2973880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973880).length < 2 ^ (prefixWord ++ tailWord_2973880).sum := by decide
  have hdescent : baseEnd_2973880 < baseStart_2973880 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973913 : List Nat := [1, 2, 1, 2, 3, 1, 3, 2, 1, 5, 2]
def baseStart_2973913 : Nat := 118140960795 + 2973913 * 2 ^ 59
def prefixEnd_2973913 : Nat := 4983230072969 + 3 ^ 40 * 2973913 * 2
def baseEnd_2973913 : Nat := 1527046793654528285410729

theorem tailTrace_2973913 : CollatzResearch.WordTrace tailWord_2973913 prefixEnd_2973913 1527046793654528285410729 := by
  unfold tailWord_2973913
  simp only [CollatzResearch.WordTrace]
  refine ⟨108467518075028579749214393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72311678716685719832809595 108467518075028579749214393)
  ·
    refine ⟨81350638556271434811910795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108467518075028579749214393 81350638556271434811910795)
    ·
      refine ⟨122025957834407152217866193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81350638556271434811910795 122025957834407152217866193)
      ·
        refine ⟨91519468375805364163399645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122025957834407152217866193 91519468375805364163399645)
        ·
          refine ⟨34319800640927011561274867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 91519468375805364163399645 34319800640927011561274867)
          ·
            refine ⟨51479700961390517341912301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34319800640927011561274867 51479700961390517341912301)
            ·
              refine ⟨19304887860521444003217113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 51479700961390517341912301 19304887860521444003217113)
              ·
                refine ⟨14478665895391083002412835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19304887860521444003217113 14478665895391083002412835)
                ·
                  refine ⟨21717998843086624503619253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14478665895391083002412835 21717998843086624503619253)
                  ·
                    refine ⟨2036062391539371047214305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21717998843086624503619253 2036062391539371047214305)
                    ·
                      refine ⟨1527046793654528285410729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036062391539371047214305 1527046793654528285410729)
                      ·
                        rfl

theorem cell23_2973913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_2973913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973913 prefixEnd_2973913 := by exact prefixLift 2973913
  have htrace : WordTrace (prefixWord ++ tailWord_2973913) baseStart_2973913 baseEnd_2973913 := by
    simpa [prefixWord, tailWord_2973913, baseEnd_2973913] using wordTrace_append hprefix tailTrace_2973913
  have hstable : (prefixWord ++ tailWord_2973913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973913).length < 2 ^ (prefixWord ++ tailWord_2973913).sum := by decide
  have hdescent : baseEnd_2973913 < baseStart_2973913 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973930 : List Nat := [3, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2]
def baseStart_2973930 : Nat := 118140960795 + 2973930 * 2 ^ 59
def prefixEnd_2973930 : Nat := 4983230072969 + 3 ^ 40 * 2973930 * 2
def baseEnd_2973930 : Nat := 1527055522825654718898151

theorem tailTrace_2973930 : CollatzResearch.WordTrace tailWord_2973930 prefixEnd_2973930 1527055522825654718898151 := by
  unfold tailWord_2973930
  simp only [CollatzResearch.WordTrace]
  refine ⟨27117034528991747913145811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72312092077311327768388829 27117034528991747913145811)
  ·
    refine ⟨40675551793487621869718717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27117034528991747913145811 40675551793487621869718717)
    ·
      refine ⟨15253331922557858201144519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40675551793487621869718717 15253331922557858201144519)
      ·
        refine ⟨22879997883836787301716779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15253331922557858201144519 22879997883836787301716779)
        ·
          refine ⟨34319996825755180952575169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22879997883836787301716779 34319996825755180952575169)
          ·
            refine ⟨25739997619316385714431377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34319996825755180952575169 25739997619316385714431377)
            ·
              refine ⟨19304998214487289285823533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25739997619316385714431377 19304998214487289285823533)
              ·
                refine ⟨7239374330432733482183825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19304998214487289285823533 7239374330432733482183825)
                ·
                  refine ⟨5429530747824550111637869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7239374330432733482183825 5429530747824550111637869)
                  ·
                    refine ⟨2036074030434206291864201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5429530747824550111637869 2036074030434206291864201)
                    ·
                      refine ⟨1527055522825654718898151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036074030434206291864201 1527055522825654718898151)
                      ·
                        rfl

theorem cell23_2973930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 3, 2, 3, 2].length) (baseStart_2973930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973930 prefixEnd_2973930 := by exact prefixLift 2973930
  have htrace : WordTrace (prefixWord ++ tailWord_2973930) baseStart_2973930 baseEnd_2973930 := by
    simpa [prefixWord, tailWord_2973930, baseEnd_2973930] using wordTrace_append hprefix tailTrace_2973930
  have hstable : (prefixWord ++ tailWord_2973930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973930).length < 2 ^ (prefixWord ++ tailWord_2973930).sum := by decide
  have hdescent : baseEnd_2973930 < baseStart_2973930 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973936 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 1, 6]
def baseStart_2973936 : Nat := 118140960795 + 2973936 * 2 ^ 59
def prefixEnd_2973936 : Nat := 4983230072969 + 3 ^ 40 * 2973936 * 2
def baseEnd_2973936 : Nat := 509019534569860565141041

theorem tailTrace_2973936 : CollatzResearch.WordTrace tailWord_2973936 prefixEnd_2973936 509019534569860565141041 := by
  unfold tailWord_2973936
  simp only [CollatzResearch.WordTrace]
  refine ⟨54234178476972627338650831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72312237969296836451534441 54234178476972627338650831)
  ·
    refine ⟨81351267715458941007976247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54234178476972627338650831 81351267715458941007976247)
    ·
      refine ⟨122026901573188411511964371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81351267715458941007976247 122026901573188411511964371)
      ·
        refine ⟨183040352359782617267946557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122026901573188411511964371 183040352359782617267946557)
        ·
          refine ⟨68640132134918481475479959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183040352359782617267946557 68640132134918481475479959)
          ·
            refine ⟨102960198202377722213219939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68640132134918481475479959 102960198202377722213219939)
            ·
              refine ⟨154440297303566583319829909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 102960198202377722213219939 154440297303566583319829909)
              ·
                refine ⟨7239388936104683593117027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 154440297303566583319829909 7239388936104683593117027)
                ·
                  refine ⟨10859083404157025389675541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7239388936104683593117027 10859083404157025389675541)
                  ·
                    refine ⟨509019534569860565141041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10859083404157025389675541 509019534569860565141041)
                    ·
                      rfl

theorem cell23_2973936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 1, 6].length) (baseStart_2973936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973936 prefixEnd_2973936 := by exact prefixLift 2973936
  have htrace : WordTrace (prefixWord ++ tailWord_2973936) baseStart_2973936 baseEnd_2973936 := by
    simpa [prefixWord, tailWord_2973936, baseEnd_2973936] using wordTrace_append hprefix tailTrace_2973936
  have hstable : (prefixWord ++ tailWord_2973936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973936).length < 2 ^ (prefixWord ++ tailWord_2973936).sum := by decide
  have hdescent : baseEnd_2973936 < baseStart_2973936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973937 : List Nat := [1, 2, 2, 2, 2, 1, 5, 3, 1, 1, 3]
def baseStart_2973937 : Nat := 118140960795 + 2973937 * 2 ^ 59
def prefixEnd_2973937 : Nat := 4983230072969 + 3 ^ 40 * 2973937 * 2
def baseEnd_2973937 : Nat := 1527059117190236191510619

theorem tailTrace_2973937 : CollatzResearch.WordTrace tailWord_2973937 prefixEnd_2973937 1527059117190236191510619 := by
  unfold tailWord_2973937
  simp only [CollatzResearch.WordTrace]
  refine ⟨108468393426941631848088065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72312262284627754565392043 108468393426941631848088065)
  ·
    refine ⟨81351295070206223886066049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108468393426941631848088065 81351295070206223886066049)
    ·
      refine ⟨61013471302654667914549537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81351295070206223886066049 61013471302654667914549537)
      ·
        refine ⟨45760103476991000935912153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 61013471302654667914549537 45760103476991000935912153)
        ·
          refine ⟨34320077607743250701934115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45760103476991000935912153 34320077607743250701934115)
          ·
            refine ⟨51480116411614876052901173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34320077607743250701934115 51480116411614876052901173)
            ·
              refine ⟨4826260913588894629959485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 51480116411614876052901173 4826260913588894629959485)
              ·
                refine ⟨1809847842595835486234807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4826260913588894629959485 1809847842595835486234807)
                ·
                  refine ⟨2714771763893753229352211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809847842595835486234807 2714771763893753229352211)
                  ·
                    refine ⟨4072157645840629844028317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2714771763893753229352211 4072157645840629844028317)
                    ·
                      refine ⟨1527059117190236191510619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4072157645840629844028317 1527059117190236191510619)
                      ·
                        rfl

theorem cell23_2973937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 5, 3, 1, 1, 3].length) (baseStart_2973937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973937 prefixEnd_2973937 := by exact prefixLift 2973937
  have htrace : WordTrace (prefixWord ++ tailWord_2973937) baseStart_2973937 baseEnd_2973937 := by
    simpa [prefixWord, tailWord_2973937, baseEnd_2973937] using wordTrace_append hprefix tailTrace_2973937
  have hstable : (prefixWord ++ tailWord_2973937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973937).length < 2 ^ (prefixWord ++ tailWord_2973937).sum := by decide
  have hdescent : baseEnd_2973937 < baseStart_2973937 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973953 : List Nat := [1, 2, 4, 1, 1, 2, 1, 3, 4, 4]
def baseStart_2973953 : Nat := 118140960795 + 2973953 * 2 ^ 59
def prefixEnd_2973953 : Nat := 4983230072969 + 3 ^ 40 * 2973953 * 2
def baseEnd_2973953 : Nat := 509022444293569376303515

theorem tailTrace_2973953 : CollatzResearch.WordTrace tailWord_2973953 prefixEnd_2973953 509022444293569376303515 := by
  unfold tailWord_2973953
  simp only [CollatzResearch.WordTrace]
  refine ⟨108468976994883666580670513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72312651329922444387113675 108468976994883666580670513)
  ·
    refine ⟨81351732746162749935502885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108468976994883666580670513 81351732746162749935502885)
    ·
      refine ⟨15253449889905515612906791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81351732746162749935502885 15253449889905515612906791)
      ·
        refine ⟨22880174834858273419360187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15253449889905515612906791 22880174834858273419360187)
        ·
          refine ⟨34320262252287410129040281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22880174834858273419360187 34320262252287410129040281)
          ·
            refine ⟨25740196689215557596780211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34320262252287410129040281 25740196689215557596780211)
            ·
              refine ⟨38610295033823336395170317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25740196689215557596780211 38610295033823336395170317)
              ·
                refine ⟨14478860637683751148188869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38610295033823336395170317 14478860637683751148188869)
                ·
                  refine ⟨2714786369565703340285413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14478860637683751148188869 2714786369565703340285413)
                  ·
                    refine ⟨509022444293569376303515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714786369565703340285413 509022444293569376303515)
                    ·
                      rfl

theorem cell23_2973953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 4, 4].length) (baseStart_2973953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973953 prefixEnd_2973953 := by exact prefixLift 2973953
  have htrace : WordTrace (prefixWord ++ tailWord_2973953) baseStart_2973953 baseEnd_2973953 := by
    simpa [prefixWord, tailWord_2973953, baseEnd_2973953] using wordTrace_append hprefix tailTrace_2973953
  have hstable : (prefixWord ++ tailWord_2973953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973953).length < 2 ^ (prefixWord ++ tailWord_2973953).sum := by decide
  have hdescent : baseEnd_2973953 < baseStart_2973953 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973954 : List Nat := [3, 4, 1, 1, 2, 3, 1, 1, 3, 1, 3]
def baseStart_2973954 : Nat := 118140960795 + 2973954 * 2 ^ 59
def prefixEnd_2973954 : Nat := 4983230072969 + 3 ^ 40 * 2973954 * 2
def baseEnd_2973954 : Nat := 1527067846361362624998041

theorem tailTrace_2973954 : CollatzResearch.WordTrace tailWord_2973954 prefixEnd_2973954 1527067846361362624998041 := by
  unfold tailWord_2973954
  simp only [CollatzResearch.WordTrace]
  refine ⟨27117253366970010937864229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72312675645253362500971277 27117253366970010937864229)
  ·
    refine ⟨5084485006306877050849543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 27117253366970010937864229 5084485006306877050849543)
    ·
      refine ⟨7626727509460315576274315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5084485006306877050849543 7626727509460315576274315)
      ·
        refine ⟨11440091264190473364411473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7626727509460315576274315 11440091264190473364411473)
        ·
          refine ⟨8580068448142855023308605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11440091264190473364411473 8580068448142855023308605)
          ·
            refine ⟨3217525668053570633740727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8580068448142855023308605 3217525668053570633740727)
            ·
              refine ⟨4826288502080355950611091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217525668053570633740727 4826288502080355950611091)
              ·
                refine ⟨7239432753120533925916637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4826288502080355950611091 7239432753120533925916637)
                ·
                  refine ⟨2714787282420200222218739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7239432753120533925916637 2714787282420200222218739)
                  ·
                    refine ⟨4072180923630300333328109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2714787282420200222218739 4072180923630300333328109)
                    ·
                      refine ⟨1527067846361362624998041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4072180923630300333328109 1527067846361362624998041)
                      ·
                        rfl

theorem cell23_2973954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 3, 1, 1, 3, 1, 3].length) (baseStart_2973954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973954 prefixEnd_2973954 := by exact prefixLift 2973954
  have htrace : WordTrace (prefixWord ++ tailWord_2973954) baseStart_2973954 baseEnd_2973954 := by
    simpa [prefixWord, tailWord_2973954, baseEnd_2973954] using wordTrace_append hprefix tailTrace_2973954
  have hstable : (prefixWord ++ tailWord_2973954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973954).length < 2 ^ (prefixWord ++ tailWord_2973954).sum := by decide
  have hdescent : baseEnd_2973954 < baseStart_2973954 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973963 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3]
def baseStart_2973963 : Nat := 118140960795 + 2973963 * 2 ^ 59
def prefixEnd_2973963 : Nat := 4983230072969 + 3 ^ 40 * 2973963 * 2
def baseEnd_2973963 : Nat := 1527072467687253089785499

theorem tailTrace_2973963 : CollatzResearch.WordTrace tailWord_2973963 prefixEnd_2973963 1527072467687253089785499 := by
  unfold tailWord_2973963
  simp only [CollatzResearch.WordTrace]
  refine ⟨108469341724847438288534543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72312894483231625525689695 108469341724847438288534543)
  ·
    refine ⟨162704012587271157432801815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108469341724847438288534543 162704012587271157432801815)
    ·
      refine ⟨244056018880906736149202723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162704012587271157432801815 244056018880906736149202723)
      ·
        refine ⟨366084028321360104223804085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244056018880906736149202723 366084028321360104223804085)
        ·
          refine ⟨34320377655127509770981633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 366084028321360104223804085 34320377655127509770981633)
          ·
            refine ⟨25740283241345632328236225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34320377655127509770981633 25740283241345632328236225)
            ·
              refine ⟨19305212431009224246177169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25740283241345632328236225 19305212431009224246177169)
              ·
                refine ⟨14478909323256918184632877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19305212431009224246177169 14478909323256918184632877)
                ·
                  refine ⟨5429590996221344319237329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14478909323256918184632877 5429590996221344319237329)
                  ·
                    refine ⟨4072193247166008239427997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5429590996221344319237329 4072193247166008239427997)
                    ·
                      refine ⟨1527072467687253089785499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4072193247166008239427997 1527072467687253089785499)
                      ·
                        rfl

theorem cell23_2973963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 3, 2, 3].length) (baseStart_2973963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973963 prefixEnd_2973963 := by exact prefixLift 2973963
  have htrace : WordTrace (prefixWord ++ tailWord_2973963) baseStart_2973963 baseEnd_2973963 := by
    simpa [prefixWord, tailWord_2973963, baseEnd_2973963] using wordTrace_append hprefix tailTrace_2973963
  have hstable : (prefixWord ++ tailWord_2973963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973963).length < 2 ^ (prefixWord ++ tailWord_2973963).sum := by decide
  have hdescent : baseEnd_2973963 < baseStart_2973963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973991 : List Nat := [1, 1, 8, 1, 1, 1, 3, 1, 1, 5]
def baseStart_2973991 : Nat := 118140960795 + 2973991 * 2 ^ 59
def prefixEnd_2973991 : Nat := 4983230072969 + 3 ^ 40 * 2973991 * 2
def baseEnd_2973991 : Nat := 509028948381859660078457

theorem tailTrace_2973991 : CollatzResearch.WordTrace tailWord_2973991 prefixEnd_2973991 509028948381859660078457 := by
  unfold tailWord_2973991
  simp only [CollatzResearch.WordTrace]
  refine ⟨108470362968745999070553827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72313575312497332713702551 108470362968745999070553827)
  ·
    refine ⟨162705544453118998605830741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108470362968745999070553827 162705544453118998605830741)
    ·
      refine ⟨1906705599059988264912079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 162705544453118998605830741 1906705599059988264912079)
      ·
        refine ⟨2860058398589982397368119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1906705599059988264912079 2860058398589982397368119)
        ·
          refine ⟨4290087597884973596052179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860058398589982397368119 4290087597884973596052179)
          ·
            refine ⟨6435131396827460394078269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290087597884973596052179 6435131396827460394078269)
            ·
              refine ⟨2413174273810297647779351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6435131396827460394078269 2413174273810297647779351)
              ·
                refine ⟨3619761410715446471669027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413174273810297647779351 3619761410715446471669027)
                ·
                  refine ⟨5429642116073169707503541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619761410715446471669027 5429642116073169707503541)
                  ·
                    refine ⟨509028948381859660078457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5429642116073169707503541 509028948381859660078457)
                    ·
                      rfl

theorem cell23_2973991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 3, 1, 1, 5].length) (baseStart_2973991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973991 prefixEnd_2973991 := by exact prefixLift 2973991
  have htrace : WordTrace (prefixWord ++ tailWord_2973991) baseStart_2973991 baseEnd_2973991 := by
    simpa [prefixWord, tailWord_2973991, baseEnd_2973991] using wordTrace_append hprefix tailTrace_2973991
  have hstable : (prefixWord ++ tailWord_2973991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973991).length < 2 ^ (prefixWord ++ tailWord_2973991).sum := by decide
  have hdescent : baseEnd_2973991 < baseStart_2973991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2973994 : List Nat := [3, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4]
def baseStart_2973994 : Nat := 118140960795 + 2973994 * 2 ^ 59
def prefixEnd_2973994 : Nat := 4983230072969 + 3 ^ 40 * 2973994 * 2
def baseEnd_2973994 : Nat := 1527088385587542468497857

theorem tailTrace_2973994 : CollatzResearch.WordTrace tailWord_2973994 prefixEnd_2973994 1527088385587542468497857 := by
  unfold tailWord_2973994
  simp only [CollatzResearch.WordTrace]
  refine ⟨27117618096933782645728259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72313648258490087055275357 27117618096933782645728259)
  ·
    refine ⟨40676427145400673968592389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27117618096933782645728259 40676427145400673968592389)
    ·
      refine ⟨7626830089762626369111073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40676427145400673968592389 7626830089762626369111073)
      ·
        refine ⟨5720122567321969776833305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7626830089762626369111073 5720122567321969776833305)
        ·
          refine ⟨4290091925491477332624979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5720122567321969776833305 4290091925491477332624979)
          ·
            refine ⟨6435137888237215998937469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290091925491477332624979 6435137888237215998937469)
            ·
              refine ⟨2413176708088955999601551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6435137888237215998937469 2413176708088955999601551)
              ·
                refine ⟨3619765062133433999402327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413176708088955999601551 3619765062133433999402327)
                ·
                  refine ⟨5429647593200150999103491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3619765062133433999402327 5429647593200150999103491)
                  ·
                    refine ⟨8144471389800226498655237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5429647593200150999103491 8144471389800226498655237)
                    ·
                      refine ⟨1527088385587542468497857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8144471389800226498655237 1527088385587542468497857)
                      ·
                        rfl

theorem cell23_2973994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_2973994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2973994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2973994 prefixEnd_2973994 := by exact prefixLift 2973994
  have htrace : WordTrace (prefixWord ++ tailWord_2973994) baseStart_2973994 baseEnd_2973994 := by
    simpa [prefixWord, tailWord_2973994, baseEnd_2973994] using wordTrace_append hprefix tailTrace_2973994
  have hstable : (prefixWord ++ tailWord_2973994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2973994).length < 2 ^ (prefixWord ++ tailWord_2973994).sum := by decide
  have hdescent : baseEnd_2973994 < baseStart_2973994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2973994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974017 : List Nat := [1, 2, 5, 2, 3, 1, 1, 8]
def baseStart_2974017 : Nat := 118140960795 + 2974017 * 2 ^ 59
def prefixEnd_2974017 : Nat := 4983230072969 + 3 ^ 40 * 2974017 * 2
def baseEnd_2974017 : Nat := 56559266505281328833713

theorem tailTrace_2974017 : CollatzResearch.WordTrace tailWord_2974017 prefixEnd_2974017 56559266505281328833713 := by
  unfold tailWord_2974017
  simp only [CollatzResearch.WordTrace]
  refine ⟨108471311266651805511000305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72314207511101203674000203 108471311266651805511000305)
  ·
    refine ⟨81353483449988854133250229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108471311266651805511000305 81353483449988854133250229)
    ·
      refine ⟨7626889073436455074992209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 81353483449988854133250229 7626889073436455074992209)
      ·
        refine ⟨5720166805077341306244157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7626889073436455074992209 5720166805077341306244157)
        ·
          refine ⟨2145062551904002989841559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5720166805077341306244157 2145062551904002989841559)
          ·
            refine ⟨3217593827856004484762339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145062551904002989841559 3217593827856004484762339)
            ·
              refine ⟨4826390741784006727143509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217593827856004484762339 4826390741784006727143509)
              ·
                refine ⟨56559266505281328833713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 4826390741784006727143509 56559266505281328833713)
                ·
                  rfl

theorem cell23_2974017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 8].length) (baseStart_2974017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974017 prefixEnd_2974017 := by exact prefixLift 2974017
  have htrace : WordTrace (prefixWord ++ tailWord_2974017) baseStart_2974017 baseEnd_2974017 := by
    simpa [prefixWord, tailWord_2974017, baseEnd_2974017] using wordTrace_append hprefix tailTrace_2974017
  have hstable : (prefixWord ++ tailWord_2974017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974017).length < 2 ^ (prefixWord ++ tailWord_2974017).sum := by decide
  have hdescent : baseEnd_2974017 < baseStart_2974017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974103 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 1, 7]
def baseStart_2974103 : Nat := 118140960795 + 2974103 * 2 ^ 59
def prefixEnd_2974103 : Nat := 4983230072969 + 3 ^ 40 * 2974103 * 2
def baseEnd_2974103 : Nat := 509048118326294180678285

theorem tailTrace_2974103 : CollatzResearch.WordTrace tailWord_2974103 prefixEnd_2974103 509048118326294180678285 := by
  unfold tailWord_2974103
  simp only [CollatzResearch.WordTrace]
  refine ⟨108474447944340242198630963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72316298629560161465753975 108474447944340242198630963)
  ·
    refine ⟨162711671916510363297946445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108474447944340242198630963 162711671916510363297946445)
    ·
      refine ⟨61016876968691386236729917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162711671916510363297946445 61016876968691386236729917)
      ·
        refine ⟨22881328863259269838773719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61016876968691386236729917 22881328863259269838773719)
        ·
          refine ⟨34321993294888904758160579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22881328863259269838773719 34321993294888904758160579)
          ·
            refine ⟨51482989942333357137240869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34321993294888904758160579 51482989942333357137240869)
            ·
              refine ⟨9653060614187504463232663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 51482989942333357137240869 9653060614187504463232663)
              ·
                refine ⟨14479590921281256694848995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9653060614187504463232663 14479590921281256694848995)
                ·
                  refine ⟨21719386381921885042273493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14479590921281256694848995 21719386381921885042273493)
                  ·
                    refine ⟨509048118326294180678285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 21719386381921885042273493 509048118326294180678285)
                    ·
                      rfl

theorem cell23_2974103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 7].length) (baseStart_2974103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974103 prefixEnd_2974103 := by exact prefixLift 2974103
  have htrace : WordTrace (prefixWord ++ tailWord_2974103) baseStart_2974103 baseEnd_2974103 := by
    simpa [prefixWord, tailWord_2974103, baseEnd_2974103] using wordTrace_append hprefix tailTrace_2974103
  have hstable : (prefixWord ++ tailWord_2974103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974103).length < 2 ^ (prefixWord ++ tailWord_2974103).sum := by decide
  have hdescent : baseEnd_2974103 < baseStart_2974103 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974153 : List Nat := [1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 4]
def baseStart_2974153 : Nat := 118140960795 + 2974153 * 2 ^ 59
def prefixEnd_2974153 : Nat := 4983230072969 + 3 ^ 40 * 2974153 * 2
def baseEnd_2974153 : Nat := 1527170029011607346409625

theorem tailTrace_2974153 : CollatzResearch.WordTrace tailWord_2974153 prefixEnd_2974153 1527170029011607346409625 := by
  unfold tailWord_2974153
  simp only [CollatzResearch.WordTrace]
  refine ⟨108476271594159100737951113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72317514396106067158634075 108476271594159100737951113)
  ·
    refine ⟨81357203695619325553463335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108476271594159100737951113 81357203695619325553463335)
    ·
      refine ⟨122035805543428988330195003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81357203695619325553463335 122035805543428988330195003)
      ·
        refine ⟨183053708315143482495292505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122035805543428988330195003 183053708315143482495292505)
        ·
          refine ⟨137290281236357611871469379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 183053708315143482495292505 137290281236357611871469379)
          ·
            refine ⟨205935421854536417807204069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137290281236357611871469379 205935421854536417807204069)
            ·
              refine ⟨38612891597725578338850763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 205935421854536417807204069 38612891597725578338850763)
              ·
                refine ⟨57919337396588367508276145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38612891597725578338850763 57919337396588367508276145)
                ·
                  refine ⟨43439503047441275631207109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57919337396588367508276145 43439503047441275631207109)
                  ·
                    refine ⟨8144906821395239180851333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43439503047441275631207109 8144906821395239180851333)
                    ·
                      refine ⟨1527170029011607346409625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8144906821395239180851333 1527170029011607346409625)
                      ·
                        rfl

theorem cell23_2974153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_2974153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974153 prefixEnd_2974153 := by exact prefixLift 2974153
  have htrace : WordTrace (prefixWord ++ tailWord_2974153) baseStart_2974153 baseEnd_2974153 := by
    simpa [prefixWord, tailWord_2974153, baseEnd_2974153] using wordTrace_append hprefix tailTrace_2974153
  have hstable : (prefixWord ++ tailWord_2974153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974153).length < 2 ^ (prefixWord ++ tailWord_2974153).sum := by decide
  have hdescent : baseEnd_2974153 < baseStart_2974153 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974184 : List Nat := [2, 1, 4, 1, 1, 4, 1, 4, 1, 4]
def baseStart_2974184 : Nat := 118140960795 + 2974184 * 2 ^ 59
def prefixEnd_2974184 : Nat := 4983230072969 + 3 ^ 40 * 2974184 * 2
def baseEnd_2974184 : Nat := 509061982303965575040661

theorem tailTrace_2974184 : CollatzResearch.WordTrace tailWord_2974184 prefixEnd_2974184 509061982303965575040661 := by
  unfold tailWord_2974184
  simp only [CollatzResearch.WordTrace]
  refine ⟨54238701128523396516164803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72318268171364528688219737 54238701128523396516164803)
  ·
    refine ⟨81358051692785094774247205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54238701128523396516164803 81358051692785094774247205)
    ·
      refine ⟨15254634692397205270171351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81358051692785094774247205 15254634692397205270171351)
      ·
        refine ⟨22881952038595807905257027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15254634692397205270171351 22881952038595807905257027)
        ·
          refine ⟨34322928057893711857885541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22881952038595807905257027 34322928057893711857885541)
          ·
            refine ⟨6435549010855070973353539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 34322928057893711857885541 6435549010855070973353539)
            ·
              refine ⟨9653323516282606460030309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6435549010855070973353539 9653323516282606460030309)
              ·
                refine ⟨1809998159302988711255683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9653323516282606460030309 1809998159302988711255683)
                ·
                  refine ⟨2714997238954483066883525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1809998159302988711255683 2714997238954483066883525)
                  ·
                    refine ⟨509061982303965575040661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2714997238954483066883525 509061982303965575040661)
                    ·
                      rfl

theorem cell23_2974184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_2974184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974184 prefixEnd_2974184 := by exact prefixLift 2974184
  have htrace : WordTrace (prefixWord ++ tailWord_2974184) baseStart_2974184 baseEnd_2974184 := by
    simpa [prefixWord, tailWord_2974184, baseEnd_2974184] using wordTrace_append hprefix tailTrace_2974184
  have hstable : (prefixWord ++ tailWord_2974184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974184).length < 2 ^ (prefixWord ++ tailWord_2974184).sum := by decide
  have hdescent : baseEnd_2974184 < baseStart_2974184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974207 : List Nat := [1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 3]
def baseStart_2974207 : Nat := 118140960795 + 2974207 * 2 ^ 59
def prefixEnd_2974207 : Nat := 4983230072969 + 3 ^ 40 * 2974207 * 2
def baseEnd_2974207 : Nat := 1527197756966950135134377

theorem tailTrace_2974207 : CollatzResearch.WordTrace tailWord_2974207 prefixEnd_2974207 1527197756966950135134377 := by
  unfold tailWord_2974207
  simp only [CollatzResearch.WordTrace]
  refine ⟨108478241135963467960416875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72318827423975645306944583 108478241135963467960416875)
  ·
    refine ⟨162717361703945201940625313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108478241135963467960416875 162717361703945201940625313)
    ·
      refine ⟨122038021277958901455468985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162717361703945201940625313 122038021277958901455468985)
      ·
        refine ⟨91528515958469176091601739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 122038021277958901455468985 91528515958469176091601739)
        ·
          refine ⟨137292773937703764137402609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91528515958469176091601739 137292773937703764137402609)
          ·
            refine ⟨102969580453277823103051957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 137292773937703764137402609 102969580453277823103051957)
            ·
              refine ⟨9653398167494795915911121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 102969580453277823103051957 9653398167494795915911121)
              ·
                refine ⟨7240048625621096936933341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9653398167494795915911121 7240048625621096936933341)
                ·
                  refine ⟨2715018234607911351350003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7240048625621096936933341 2715018234607911351350003)
                  ·
                    refine ⟨4072527351911867027025005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715018234607911351350003 4072527351911867027025005)
                    ·
                      refine ⟨1527197756966950135134377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4072527351911867027025005 1527197756966950135134377)
                      ·
                        rfl

theorem cell23_2974207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 5, 2, 3, 1, 3].length) (baseStart_2974207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974207 prefixEnd_2974207 := by exact prefixLift 2974207
  have htrace : WordTrace (prefixWord ++ tailWord_2974207) baseStart_2974207 baseEnd_2974207 := by
    simpa [prefixWord, tailWord_2974207, baseEnd_2974207] using wordTrace_append hprefix tailTrace_2974207
  have hstable : (prefixWord ++ tailWord_2974207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974207).length < 2 ^ (prefixWord ++ tailWord_2974207).sum := by decide
  have hdescent : baseEnd_2974207 < baseStart_2974207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974217 : List Nat := [1, 2, 1, 1, 3, 1, 2, 5, 2, 3, 2]
def baseStart_2974217 : Nat := 118140960795 + 2974217 * 2 ^ 59
def prefixEnd_2974217 : Nat := 4983230072969 + 3 ^ 40 * 2974217 * 2
def baseEnd_2974217 : Nat := 1527202891773495096009331

theorem tailTrace_2974217 : CollatzResearch.WordTrace tailWord_2974217 prefixEnd_2974217 1527202891773495096009331 := by
  unfold tailWord_2974217
  simp only [CollatzResearch.WordTrace]
  refine ⟨108478605865927239668280905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72319070577284826445520603 108478605865927239668280905)
  ·
    refine ⟨81358954399445429751210679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108478605865927239668280905 81358954399445429751210679)
    ·
      refine ⟨122038431599168144626816019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81358954399445429751210679 122038431599168144626816019)
      ·
        refine ⟨183057647398752216940224029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122038431599168144626816019 183057647398752216940224029)
        ·
          refine ⟨68646617774532081352584011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183057647398752216940224029 68646617774532081352584011)
          ·
            refine ⟨102969926661798122028876017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 68646617774532081352584011 102969926661798122028876017)
            ·
              refine ⟨77227444996348591521657013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 102969926661798122028876017 77227444996348591521657013)
              ·
                refine ⟨7240072968407680455155345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 77227444996348591521657013 7240072968407680455155345)
                ·
                  refine ⟨5430054726305760341366509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7240072968407680455155345 5430054726305760341366509)
                  ·
                    refine ⟨2036270522364660128012441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5430054726305760341366509 2036270522364660128012441)
                    ·
                      refine ⟨1527202891773495096009331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036270522364660128012441 1527202891773495096009331)
                      ·
                        rfl

theorem cell23_2974217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 5, 2, 3, 2].length) (baseStart_2974217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974217 prefixEnd_2974217 := by exact prefixLift 2974217
  have htrace : WordTrace (prefixWord ++ tailWord_2974217) baseStart_2974217 baseEnd_2974217 := by
    simpa [prefixWord, tailWord_2974217, baseEnd_2974217] using wordTrace_append hprefix tailTrace_2974217
  have hstable : (prefixWord ++ tailWord_2974217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974217).length < 2 ^ (prefixWord ++ tailWord_2974217).sum := by decide
  have hdescent : baseEnd_2974217 < baseStart_2974217 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974231 : List Nat := [1, 1, 3, 6, 2, 1, 1, 2, 6]
def baseStart_2974231 : Nat := 118140960795 + 2974231 * 2 ^ 59
def prefixEnd_2974231 : Nat := 4983230072969 + 3 ^ 40 * 2974231 * 2
def baseEnd_2974231 : Nat := 169690008944739782359363

theorem tailTrace_2974231 : CollatzResearch.WordTrace tailWord_2974231 prefixEnd_2974231 169690008944739782359363 := by
  unfold tailWord_2974231
  simp only [CollatzResearch.WordTrace]
  refine ⟨108479116487876520059290547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72319410991917680039527031 108479116487876520059290547)
  ·
    refine ⟨162718674731814780088935821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108479116487876520059290547 162718674731814780088935821)
    ·
      refine ⟨61019503024430542533350933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 162718674731814780088935821 61019503024430542533350933)
      ·
        refine ⟨2860289204270181681250825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 61019503024430542533350933 2860289204270181681250825)
        ·
          refine ⟨2145216903202636260938119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2860289204270181681250825 2145216903202636260938119)
          ·
            refine ⟨3217825354803954391407179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145216903202636260938119 3217825354803954391407179)
            ·
              refine ⟨4826738032205931587110769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3217825354803954391407179 4826738032205931587110769)
              ·
                refine ⟨3620053524154448690333077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4826738032205931587110769 3620053524154448690333077)
                ·
                  refine ⟨169690008944739782359363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3620053524154448690333077 169690008944739782359363)
                  ·
                    rfl

theorem cell23_2974231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 1, 2, 6].length) (baseStart_2974231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974231 prefixEnd_2974231 := by exact prefixLift 2974231
  have htrace : WordTrace (prefixWord ++ tailWord_2974231) baseStart_2974231 baseEnd_2974231 := by
    simpa [prefixWord, tailWord_2974231, baseEnd_2974231] using wordTrace_append hprefix tailTrace_2974231
  have hstable : (prefixWord ++ tailWord_2974231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974231).length < 2 ^ (prefixWord ++ tailWord_2974231).sum := by decide
  have hdescent : baseEnd_2974231 < baseStart_2974231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974257 : List Nat := [1, 2, 2, 3, 1, 1, 2, 5, 2, 4]
def baseStart_2974257 : Nat := 118140960795 + 2974257 * 2 ^ 59
def prefixEnd_2974257 : Nat := 4983230072969 + 3 ^ 40 * 2974257 * 2
def baseEnd_2974257 : Nat := 509074476999891646503049

theorem tailTrace_2974257 : CollatzResearch.WordTrace tailWord_2974257 prefixEnd_2974257 509074476999891646503049 := by
  unfold tailWord_2974257
  simp only [CollatzResearch.WordTrace]
  refine ⟨108480064785782326499737025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72320043190521550999824683 108480064785782326499737025)
  ·
    refine ⟨81360048589336744874802769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108480064785782326499737025 81360048589336744874802769)
    ·
      refine ⟨61020036442002558656102077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81360048589336744874802769 61020036442002558656102077)
      ·
        refine ⟨22882513665750959496038279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61020036442002558656102077 22882513665750959496038279)
        ·
          refine ⟨34323770498626439244057419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22882513665750959496038279 34323770498626439244057419)
          ·
            refine ⟨51485655747939658866086129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34323770498626439244057419 51485655747939658866086129)
            ·
              refine ⟨38614241810954744149564597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51485655747939658866086129 38614241810954744149564597)
              ·
                refine ⟨3620085169777007264021681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38614241810954744149564597 3620085169777007264021681)
                ·
                  refine ⟨2715063877332755448016261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620085169777007264021681 2715063877332755448016261)
                  ·
                    refine ⟨509074476999891646503049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2715063877332755448016261 509074476999891646503049)
                    ·
                      rfl

theorem cell23_2974257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 4].length) (baseStart_2974257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974257 prefixEnd_2974257 := by exact prefixLift 2974257
  have htrace : WordTrace (prefixWord ++ tailWord_2974257) baseStart_2974257 baseEnd_2974257 := by
    simpa [prefixWord, tailWord_2974257, baseEnd_2974257] using wordTrace_append hprefix tailTrace_2974257
  have hstable : (prefixWord ++ tailWord_2974257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974257).length < 2 ^ (prefixWord ++ tailWord_2974257).sum := by decide
  have hdescent : baseEnd_2974257 < baseStart_2974257 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974264 : List Nat := [2, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2]
def baseStart_2974264 : Nat := 118140960795 + 2974264 * 2 ^ 59
def prefixEnd_2974264 : Nat := 4983230072969 + 3 ^ 40 * 2974264 * 2
def baseEnd_2974264 : Nat := 1527227025364256412121615

theorem tailTrace_2974264 : CollatzResearch.WordTrace tailWord_2974264 prefixEnd_2974264 1527227025364256412121615 := by
  unfold tailWord_2974264
  simp only [CollatzResearch.WordTrace]
  refine ⟨54240160048378483347620923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72320213397837977796827897 54240160048378483347620923)
  ·
    refine ⟨81360240072567725021431385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54240160048378483347620923 81360240072567725021431385)
    ·
      refine ⟨61020180054425793766073539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 81360240072567725021431385 61020180054425793766073539)
      ·
        refine ⟨91530270081638690649110309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61020180054425793766073539 91530270081638690649110309)
        ·
          refine ⟨17161925640307254496708183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 91530270081638690649110309 17161925640307254496708183)
          ·
            refine ⟨25742888460460881745062275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17161925640307254496708183 25742888460460881745062275)
            ·
              refine ⟨38614332690691322617593413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25742888460460881745062275 38614332690691322617593413)
              ·
                refine ⟨7240187379504622990798765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38614332690691322617593413 7240187379504622990798765)
                ·
                  refine ⟨2715070267314233621549537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7240187379504622990798765 2715070267314233621549537)
                  ·
                    refine ⟨2036302700485675216162153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715070267314233621549537 2036302700485675216162153)
                    ·
                      refine ⟨1527227025364256412121615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036302700485675216162153 1527227025364256412121615)
                      ·
                        rfl

theorem cell23_2974264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 4, 3, 2, 2].length) (baseStart_2974264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974264 prefixEnd_2974264 := by exact prefixLift 2974264
  have htrace : WordTrace (prefixWord ++ tailWord_2974264) baseStart_2974264 baseEnd_2974264 := by
    simpa [prefixWord, tailWord_2974264, baseEnd_2974264] using wordTrace_append hprefix tailTrace_2974264
  have hstable : (prefixWord ++ tailWord_2974264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974264).length < 2 ^ (prefixWord ++ tailWord_2974264).sum := by decide
  have hdescent : baseEnd_2974264 < baseStart_2974264 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974394 : List Nat := [3, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_2974394 : Nat := 118140960795 + 2974394 * 2 ^ 59
def prefixEnd_2974394 : Nat := 4983230072969 + 3 ^ 40 * 2974394 * 2
def baseEnd_2974394 : Nat := 169699308649926767055113

theorem tailTrace_2974394 : CollatzResearch.WordTrace tailWord_2974394 prefixEnd_2974394 169699308649926767055113 := by
  unfold tailWord_2974394
  simp only [CollatzResearch.WordTrace]
  refine ⟨27121265396571499724368559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72323374390857332598316157 27121265396571499724368559)
  ·
    refine ⟨40681898094857249586552839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27121265396571499724368559 40681898094857249586552839)
    ·
      refine ⟨61022847142285874379829259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40681898094857249586552839 61022847142285874379829259)
      ·
        refine ⟨91534270713428811569743889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61022847142285874379829259 91534270713428811569743889)
        ·
          refine ⟨68650703035071608677307917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91534270713428811569743889 68650703035071608677307917)
          ·
            refine ⟨25744013638151853253990469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68650703035071608677307917 25744013638151853253990469)
            ·
              refine ⟨4827002557153472485123213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25744013638151853253990469 4827002557153472485123213)
              ·
                refine ⟨1810125958932552181921205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827002557153472485123213 1810125958932552181921205)
                ·
                  refine ⟨169699308649926767055113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1810125958932552181921205 169699308649926767055113)
                  ·
                    rfl

theorem cell23_2974394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_2974394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974394 prefixEnd_2974394 := by exact prefixLift 2974394
  have htrace : WordTrace (prefixWord ++ tailWord_2974394) baseStart_2974394 baseEnd_2974394 := by
    simpa [prefixWord, tailWord_2974394, baseEnd_2974394] using wordTrace_append hprefix tailTrace_2974394
  have hstable : (prefixWord ++ tailWord_2974394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974394).length < 2 ^ (prefixWord ++ tailWord_2974394).sum := by decide
  have hdescent : baseEnd_2974394 < baseStart_2974394 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974404 : List Nat := [2, 3, 3, 1, 1, 2, 1, 2, 2, 3, 3]
def baseStart_2974404 : Nat := 118140960795 + 2974404 * 2 ^ 59
def prefixEnd_2974404 : Nat := 4983230072969 + 3 ^ 40 * 2974404 * 2
def baseEnd_2974404 : Nat := 1527298912655885864370971

theorem tailTrace_2974404 : CollatzResearch.WordTrace tailWord_2974404 prefixEnd_2974404 1527298912655885864370971 := by
  unfold tailWord_2974404
  simp only [CollatzResearch.WordTrace]
  refine ⟨54242713158124885302669133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72323617544166513736892177 54242713158124885302669133)
  ·
    refine ⟨20341017434296831988500925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54242713158124885302669133 20341017434296831988500925)
    ·
      refine ⟨7627881537861311995687847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20341017434296831988500925 7627881537861311995687847)
      ·
        refine ⟨11441822306791967993531771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7627881537861311995687847 11441822306791967993531771)
        ·
          refine ⟨17162733460187951990297657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11441822306791967993531771 17162733460187951990297657)
          ·
            refine ⟨12872050095140963992723243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17162733460187951990297657 12872050095140963992723243)
            ·
              refine ⟨19308075142711445989084865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12872050095140963992723243 19308075142711445989084865)
              ·
                refine ⟨14481056357033584491813649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19308075142711445989084865 14481056357033584491813649)
                ·
                  refine ⟨10860792267775188368860237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14481056357033584491813649 10860792267775188368860237)
                  ·
                    refine ⟨4072797100415695638322589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10860792267775188368860237 4072797100415695638322589)
                    ·
                      refine ⟨1527298912655885864370971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4072797100415695638322589 1527298912655885864370971)
                      ·
                        rfl

theorem cell23_2974404_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_2974404 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974404 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974404 prefixEnd_2974404 := by exact prefixLift 2974404
  have htrace : WordTrace (prefixWord ++ tailWord_2974404) baseStart_2974404 baseEnd_2974404 := by
    simpa [prefixWord, tailWord_2974404, baseEnd_2974404] using wordTrace_append hprefix tailTrace_2974404
  have hstable : (prefixWord ++ tailWord_2974404).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974404).length < 2 ^ (prefixWord ++ tailWord_2974404).sum := by decide
  have hdescent : baseEnd_2974404 < baseStart_2974404 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974404) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974467 : List Nat := [1, 1, 1, 3, 2, 2, 1, 6, 6]
def baseStart_2974467 : Nat := 118140960795 + 2974467 * 2 ^ 59
def prefixEnd_2974467 : Nat := 4983230072969 + 3 ^ 40 * 2974467 * 2
def baseEnd_2974467 : Nat := 169703473548568790875909

theorem tailTrace_2974467 : CollatzResearch.WordTrace tailWord_2974467 prefixEnd_2974467 169703473548568790875909 := by
  unfold tailWord_2974467
  simp only [CollatzResearch.WordTrace]
  refine ⟨108487724115021532364881655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72325149410014354909921103 108487724115021532364881655)
  ·
    refine ⟨162731586172532298547322483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108487724115021532364881655 162731586172532298547322483)
    ·
      refine ⟨244097379258798447820983725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162731586172532298547322483 244097379258798447820983725)
      ·
        refine ⟨91536517222049417932868897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 244097379258798447820983725 91536517222049417932868897)
        ·
          refine ⟨68652387916537063449651673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 91536517222049417932868897 68652387916537063449651673)
          ·
            refine ⟨51489290937402797587238755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68652387916537063449651673 51489290937402797587238755)
            ·
              refine ⟨77233936406104196380858133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51489290937402797587238755 77233936406104196380858133)
              ·
                refine ⟨3620340769036134205352725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 77233936406104196380858133 3620340769036134205352725)
                ·
                  refine ⟨169703473548568790875909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3620340769036134205352725 169703473548568790875909)
                  ·
                    rfl

theorem cell23_2974467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 1, 6, 6].length) (baseStart_2974467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974467 prefixEnd_2974467 := by exact prefixLift 2974467
  have htrace : WordTrace (prefixWord ++ tailWord_2974467) baseStart_2974467 baseEnd_2974467 := by
    simpa [prefixWord, tailWord_2974467, baseEnd_2974467] using wordTrace_append hprefix tailTrace_2974467
  have hstable : (prefixWord ++ tailWord_2974467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974467).length < 2 ^ (prefixWord ++ tailWord_2974467).sum := by decide
  have hdescent : baseEnd_2974467 < baseStart_2974467 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974471 : List Nat := [1, 1, 4, 4, 1, 1, 3, 1, 3, 4]
def baseStart_2974471 : Nat := 118140960795 + 2974471 * 2 ^ 59
def prefixEnd_2974471 : Nat := 4983230072969 + 3 ^ 40 * 2974471 * 2
def baseEnd_2974471 : Nat := 509111105286579034077721

theorem tailTrace_2974471 : CollatzResearch.WordTrace tailWord_2974471 prefixEnd_2974471 509111105286579034077721 := by
  unfold tailWord_2974471
  simp only [CollatzResearch.WordTrace]
  refine ⟨108487870007007041048027267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72325246671338027365351511 108487870007007041048027267)
  ·
    refine ⟨162731805010510561572040901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108487870007007041048027267 162731805010510561572040901)
    ·
      refine ⟨30512213439470730294757669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 162731805010510561572040901 30512213439470730294757669)
      ·
        refine ⟨5721040019900761930267063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30512213439470730294757669 5721040019900761930267063)
        ·
          refine ⟨8581560029851142895400595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5721040019900761930267063 8581560029851142895400595)
          ·
            refine ⟨12872340044776714343100893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8581560029851142895400595 12872340044776714343100893)
            ·
              refine ⟨4827127516791267878662835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12872340044776714343100893 4827127516791267878662835)
              ·
                refine ⟨7240691275186901817994253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827127516791267878662835 7240691275186901817994253)
                ·
                  refine ⟨2715259228195088181747845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7240691275186901817994253 2715259228195088181747845)
                  ·
                    refine ⟨509111105286579034077721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2715259228195088181747845 509111105286579034077721)
                    ·
                      rfl

theorem cell23_2974471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 4].length) (baseStart_2974471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974471 prefixEnd_2974471 := by exact prefixLift 2974471
  have htrace : WordTrace (prefixWord ++ tailWord_2974471) baseStart_2974471 baseEnd_2974471 := by
    simpa [prefixWord, tailWord_2974471, baseEnd_2974471] using wordTrace_append hprefix tailTrace_2974471
  have hstable : (prefixWord ++ tailWord_2974471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974471).length < 2 ^ (prefixWord ++ tailWord_2974471).sum := by decide
  have hdescent : baseEnd_2974471 < baseStart_2974471 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974518 : List Nat := [5, 1, 2, 2, 2, 1, 2, 2, 6]
def baseStart_2974518 : Nat := 118140960795 + 2974518 * 2 ^ 59
def prefixEnd_2974518 : Nat := 4983230072969 + 3 ^ 40 * 2974518 * 2
def baseEnd_2974518 : Nat := 169706383272277602038383

theorem tailTrace_2974518 : CollatzResearch.WordTrace tailWord_2974518 prefixEnd_2974518 169706383272277602038383 := by
  unfold tailWord_2974518
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780599014864798004686763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72326389491891178716658805 6780599014864798004686763)
  ·
    refine ⟨10170898522297197007030145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6780599014864798004686763 10170898522297197007030145)
    ·
      refine ⟨7628173891722897755272609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10170898522297197007030145 7628173891722897755272609)
      ·
        refine ⟨5721130418792173316454457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7628173891722897755272609 5721130418792173316454457)
        ·
          refine ⟨4290847814094129987340843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5721130418792173316454457 4290847814094129987340843)
          ·
            refine ⟨6436271721141194981011265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290847814094129987340843 6436271721141194981011265)
            ·
              refine ⟨4827203790855896235758449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436271721141194981011265 4827203790855896235758449)
              ·
                refine ⟨3620402843141922176818837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827203790855896235758449 3620402843141922176818837)
                ·
                  refine ⟨169706383272277602038383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3620402843141922176818837 169706383272277602038383)
                  ·
                    rfl

theorem cell23_2974518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_2974518 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974518 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974518 prefixEnd_2974518 := by exact prefixLift 2974518
  have htrace : WordTrace (prefixWord ++ tailWord_2974518) baseStart_2974518 baseEnd_2974518 := by
    simpa [prefixWord, tailWord_2974518, baseEnd_2974518] using wordTrace_append hprefix tailTrace_2974518
  have hstable : (prefixWord ++ tailWord_2974518).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974518).length < 2 ^ (prefixWord ++ tailWord_2974518).sum := by decide
  have hdescent : baseEnd_2974518 < baseStart_2974518 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974522 : List Nat := [3, 1, 1, 1, 7, 1, 2, 2, 1, 4]
def baseStart_2974522 : Nat := 118140960795 + 2974522 * 2 ^ 59
def prefixEnd_2974522 : Nat := 4983230072969 + 3 ^ 40 * 2974522 * 2
def baseEnd_2974522 : Nat := 509119834457705467565143

theorem tailTrace_2974522 : CollatzResearch.WordTrace tailWord_2974522 prefixEnd_2974522 509119834457705467565143 := by
  unfold tailWord_2974522
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122432532455569189533455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72326486753214851172089213 27122432532455569189533455)
  ·
    refine ⟨40683648798683353784300183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27122432532455569189533455 40683648798683353784300183)
    ·
      refine ⟨61025473198025030676450275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40683648798683353784300183 61025473198025030676450275)
      ·
        refine ⟨91538209797037546014675413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61025473198025030676450275 91538209797037546014675413)
        ·
          refine ⟨2145426792118067484718955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 91538209797037546014675413 2145426792118067484718955)
          ·
            refine ⟨3218140188177101227078433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2145426792118067484718955 3218140188177101227078433)
            ·
              refine ⟨2413605141132825920308825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218140188177101227078433 2413605141132825920308825)
              ·
                refine ⟨1810203855849619440231619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413605141132825920308825 1810203855849619440231619)
                ·
                  refine ⟨2715305783774429160347429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810203855849619440231619 2715305783774429160347429)
                  ·
                    refine ⟨509119834457705467565143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2715305783774429160347429 509119834457705467565143)
                    ·
                      rfl

theorem cell23_2974522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 7, 1, 2, 2, 1, 4].length) (baseStart_2974522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974522 prefixEnd_2974522 := by exact prefixLift 2974522
  have htrace : WordTrace (prefixWord ++ tailWord_2974522) baseStart_2974522 baseEnd_2974522 := by
    simpa [prefixWord, tailWord_2974522, baseEnd_2974522] using wordTrace_append hprefix tailTrace_2974522
  have hstable : (prefixWord ++ tailWord_2974522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974522).length < 2 ^ (prefixWord ++ tailWord_2974522).sum := by decide
  have hdescent : baseEnd_2974522 < baseStart_2974522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974547 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6]
def baseStart_2974547 : Nat := 118140960795 + 2974547 * 2 ^ 59
def prefixEnd_2974547 : Nat := 4983230072969 + 3 ^ 40 * 2974547 * 2
def baseEnd_2974547 : Nat := 1527372340389478804882813

theorem tailTrace_2974547 : CollatzResearch.WordTrace tailWord_2974547 prefixEnd_2974547 1527372340389478804882813 := by
  unfold tailWord_2974547
  simp only [CollatzResearch.WordTrace]
  refine ⟨108490641954731706027793895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72327094636487804018529263 108490641954731706027793895)
  ·
    refine ⟨162735962932097559041690843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108490641954731706027793895 162735962932097559041690843)
    ·
      refine ⟨244103944398146338562536265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162735962932097559041690843 244103944398146338562536265)
      ·
        refine ⟨183077958298609753921902199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244103944398146338562536265 183077958298609753921902199)
        ·
          refine ⟨274616937447914630882853299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183077958298609753921902199 274616937447914630882853299)
          ·
            refine ⟨411925406171871946324279949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274616937447914630882853299 411925406171871946324279949)
            ·
              refine ⟨154472027314451979871604981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 411925406171871946324279949 154472027314451979871604981)
              ·
                refine ⟨14481752560729873112962967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 154472027314451979871604981 14481752560729873112962967)
                ·
                  refine ⟨21722628841094809669444451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14481752560729873112962967 21722628841094809669444451)
                  ·
                    refine ⟨32583943261642214504166677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21722628841094809669444451 32583943261642214504166677)
                    ·
                      refine ⟨1527372340389478804882813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32583943261642214504166677 1527372340389478804882813)
                      ·
                        rfl

theorem cell23_2974547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 1, 1, 6].length) (baseStart_2974547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974547 prefixEnd_2974547 := by exact prefixLift 2974547
  have htrace : WordTrace (prefixWord ++ tailWord_2974547) baseStart_2974547 baseEnd_2974547 := by
    simpa [prefixWord, tailWord_2974547, baseEnd_2974547] using wordTrace_append hprefix tailTrace_2974547
  have hstable : (prefixWord ++ tailWord_2974547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974547).length < 2 ^ (prefixWord ++ tailWord_2974547).sum := by decide
  have hdescent : baseEnd_2974547 < baseStart_2974547 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974562 : List Nat := [3, 3, 2, 1, 3, 1, 2, 3, 1, 1, 3]
def baseStart_2974562 : Nat := 118140960795 + 2974562 * 2 ^ 59
def prefixEnd_2974562 : Nat := 4983230072969 + 3 ^ 40 * 2974562 * 2
def baseEnd_2974562 : Nat := 1527380042599296246195245

theorem tailTrace_2974562 : CollatzResearch.WordTrace tailWord_2974562 prefixEnd_2974562 1527380042599296246195245 := by
  unfold tailWord_2974562
  simp only [CollatzResearch.WordTrace]
  refine ⟨27122797262419340897397485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72327459366451575726393293 27122797262419340897397485)
  ·
    refine ⟨10171048973407252836524057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 27122797262419340897397485 10171048973407252836524057)
    ·
      refine ⟨7628286730055439627393043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10171048973407252836524057 7628286730055439627393043)
      ·
        refine ⟨11442430095083159441089565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7628286730055439627393043 11442430095083159441089565)
        ·
          refine ⟨4290911285656184790408587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11442430095083159441089565 4290911285656184790408587)
          ·
            refine ⟨6436366928484277185612881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4290911285656184790408587 6436366928484277185612881)
            ·
              refine ⟨4827275196363207889209661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6436366928484277185612881 4827275196363207889209661)
              ·
                refine ⟨1810228198636202958453623, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4827275196363207889209661 1810228198636202958453623)
                ·
                  refine ⟨2715342297954304437680435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810228198636202958453623 2715342297954304437680435)
                  ·
                    refine ⟨4073013446931456656520653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715342297954304437680435 4073013446931456656520653)
                    ·
                      refine ⟨1527380042599296246195245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073013446931456656520653 1527380042599296246195245)
                      ·
                        rfl

theorem cell23_2974562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 1, 2, 3, 1, 1, 3].length) (baseStart_2974562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974562 prefixEnd_2974562 := by exact prefixLift 2974562
  have htrace : WordTrace (prefixWord ++ tailWord_2974562) baseStart_2974562 baseEnd_2974562 := by
    simpa [prefixWord, tailWord_2974562, baseEnd_2974562] using wordTrace_append hprefix tailTrace_2974562
  have hstable : (prefixWord ++ tailWord_2974562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974562).length < 2 ^ (prefixWord ++ tailWord_2974562).sum := by decide
  have hdescent : baseEnd_2974562 < baseStart_2974562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974568 : List Nat := [2, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4]
def baseStart_2974568 : Nat := 118140960795 + 2974568 * 2 ^ 59
def prefixEnd_2974568 : Nat := 4983230072969 + 3 ^ 40 * 2974568 * 2
def baseEnd_2974568 : Nat := 1527383123483223222720217

theorem tailTrace_2974568 : CollatzResearch.WordTrace tailWord_2974568 prefixEnd_2974568 1527383123483223222720217 := by
  unfold tailWord_2974568
  simp only [CollatzResearch.WordTrace]
  refine ⟨54245703943827813307154179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72327605258437084409538905 54245703943827813307154179)
  ·
    refine ⟨81368555915741719960731269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54245703943827813307154179 81368555915741719960731269)
    ·
      refine ⟨15256604234201572492637113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 81368555915741719960731269 15256604234201572492637113)
      ·
        refine ⟨11442453175651179369477835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15256604234201572492637113 11442453175651179369477835)
        ·
          refine ⟨17163679763476769054216753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11442453175651179369477835 17163679763476769054216753)
          ·
            refine ⟨12872759822607576790662565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17163679763476769054216753 12872759822607576790662565)
            ·
              refine ⟨2413642466738920648249231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12872759822607576790662565 2413642466738920648249231)
              ·
                refine ⟨3620463700108380972373847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413642466738920648249231 3620463700108380972373847)
                ·
                  refine ⟨5430695550162571458560771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620463700108380972373847 5430695550162571458560771)
                  ·
                    refine ⟨8146043325243857187841157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5430695550162571458560771 8146043325243857187841157)
                    ·
                      refine ⟨1527383123483223222720217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8146043325243857187841157 1527383123483223222720217)
                      ·
                        rfl

theorem cell23_2974568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 4, 1, 1, 1, 4].length) (baseStart_2974568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974568 prefixEnd_2974568 := by exact prefixLift 2974568
  have htrace : WordTrace (prefixWord ++ tailWord_2974568) baseStart_2974568 baseEnd_2974568 := by
    simpa [prefixWord, tailWord_2974568, baseEnd_2974568] using wordTrace_append hprefix tailTrace_2974568
  have hstable : (prefixWord ++ tailWord_2974568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974568).length < 2 ^ (prefixWord ++ tailWord_2974568).sum := by decide
  have hdescent : baseEnd_2974568 < baseStart_2974568 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974585 : List Nat := [1, 2, 1, 3, 2, 3, 2, 4, 1, 2, 2]
def baseStart_2974585 : Nat := 118140960795 + 2974585 * 2 ^ 59
def prefixEnd_2974585 : Nat := 4983230072969 + 3 ^ 40 * 2974585 * 2
def baseEnd_2974585 : Nat := 1527391852654349656207639

theorem tailTrace_2974585 : CollatzResearch.WordTrace tailWord_2974585 prefixEnd_2974585 1527391852654349656207639 := by
  unfold tailWord_2974585
  simp only [CollatzResearch.WordTrace]
  refine ⟨108492027928594038517677209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72328018619062692345118139 108492027928594038517677209)
  ·
    refine ⟨81369020946445528888257907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108492027928594038517677209 81369020946445528888257907)
    ·
      refine ⟨122053531419668293332386861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81369020946445528888257907 122053531419668293332386861)
      ·
        refine ⟨45770074282375609999645073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122053531419668293332386861 45770074282375609999645073)
        ·
          refine ⟨34327555711781707499733805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45770074282375609999645073 34327555711781707499733805)
          ·
            refine ⟨12872833391918140312400177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 34327555711781707499733805 12872833391918140312400177)
            ·
              refine ⟨9654625043938605234300133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12872833391918140312400177 9654625043938605234300133)
              ·
                refine ⟨1810242195738488481431275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9654625043938605234300133 1810242195738488481431275)
                ·
                  refine ⟨2715363293607732722146913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810242195738488481431275 2715363293607732722146913)
                  ·
                    refine ⟨2036522470205799541610185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2715363293607732722146913 2036522470205799541610185)
                    ·
                      refine ⟨1527391852654349656207639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036522470205799541610185 1527391852654349656207639)
                      ·
                        rfl

theorem cell23_2974585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_2974585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974585 prefixEnd_2974585 := by exact prefixLift 2974585
  have htrace : WordTrace (prefixWord ++ tailWord_2974585) baseStart_2974585 baseEnd_2974585 := by
    simpa [prefixWord, tailWord_2974585, baseEnd_2974585] using wordTrace_append hprefix tailTrace_2974585
  have hstable : (prefixWord ++ tailWord_2974585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974585).length < 2 ^ (prefixWord ++ tailWord_2974585).sum := by decide
  have hdescent : baseEnd_2974585 < baseStart_2974585 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974587 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 1, 9]
def baseStart_2974587 : Nat := 118140960795 + 2974587 * 2 ^ 59
def prefixEnd_2974587 : Nat := 4983230072969 + 3 ^ 40 * 2974587 * 2
def baseEnd_2974587 : Nat := 509130959871886216127543

theorem tailTrace_2974587 : CollatzResearch.WordTrace tailWord_2974587 prefixEnd_2974587 509130959871886216127543 := by
  unfold tailWord_2974587
  simp only [CollatzResearch.WordTrace]
  refine ⟨108492100874586792859250015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72328067249724528572833343 108492100874586792859250015)
  ·
    refine ⟨162738151311880189288875023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108492100874586792859250015 162738151311880189288875023)
    ·
      refine ⟨244107226967820283933312535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162738151311880189288875023 244107226967820283933312535)
      ·
        refine ⟨366160840451730425899968803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244107226967820283933312535 366160840451730425899968803)
        ·
          refine ⟨549241260677595638849953205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366160840451730425899968803 549241260677595638849953205)
          ·
            refine ⟨51491368188524591142183113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 549241260677595638849953205 51491368188524591142183113)
            ·
              refine ⟨38618526141393443356637335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51491368188524591142183113 38618526141393443356637335)
              ·
                refine ⟨57927789212090165034956003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38618526141393443356637335 57927789212090165034956003)
                ·
                  refine ⟨86891683818135247552434005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57927789212090165034956003 86891683818135247552434005)
                  ·
                    refine ⟨509130959871886216127543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 86891683818135247552434005 509130959871886216127543)
                    ·
                      rfl

theorem cell23_2974587_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 1, 9].length) (baseStart_2974587 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974587 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974587 prefixEnd_2974587 := by exact prefixLift 2974587
  have htrace : WordTrace (prefixWord ++ tailWord_2974587) baseStart_2974587 baseEnd_2974587 := by
    simpa [prefixWord, tailWord_2974587, baseEnd_2974587] using wordTrace_append hprefix tailTrace_2974587
  have hstable : (prefixWord ++ tailWord_2974587).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974587).length < 2 ^ (prefixWord ++ tailWord_2974587).sum := by decide
  have hdescent : baseEnd_2974587 < baseStart_2974587 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974587) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974601 : List Nat := [1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 3]
def baseStart_2974601 : Nat := 118140960795 + 2974601 * 2 ^ 59
def prefixEnd_2974601 : Nat := 4983230072969 + 3 ^ 40 * 2974601 * 2
def baseEnd_2974601 : Nat := 1527400068344821593607565

theorem tailTrace_2974601 : CollatzResearch.WordTrace tailWord_2974601 prefixEnd_2974601 1527400068344821593607565 := by
  unfold tailWord_2974601
  simp only [CollatzResearch.WordTrace]
  refine ⟨108492611496536073250259657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72328407664357382166839771 108492611496536073250259657)
  ·
    refine ⟨81369458622402054937694743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108492611496536073250259657 81369458622402054937694743)
    ·
      refine ⟨122054187933603082406542115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81369458622402054937694743 122054187933603082406542115)
      ·
        refine ⟨183081281900404623609813173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122054187933603082406542115 183081281900404623609813173)
        ·
          refine ⟨17163870178162933463419985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 183081281900404623609813173 17163870178162933463419985)
          ·
            refine ⟨12872902633622200097564989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17163870178162933463419985 12872902633622200097564989)
            ·
              refine ⟨4827338487608325036586871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12872902633622200097564989 4827338487608325036586871)
              ·
                refine ⟨7241007731412487554880307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827338487608325036586871 7241007731412487554880307)
                ·
                  refine ⟨10861511597118731332320461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241007731412487554880307 10861511597118731332320461)
                  ·
                    refine ⟨4073066848919524249620173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861511597118731332320461 4073066848919524249620173)
                    ·
                      refine ⟨1527400068344821593607565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073066848919524249620173 1527400068344821593607565)
                      ·
                        rfl

theorem cell23_2974601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_2974601 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974601 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974601 prefixEnd_2974601 := by exact prefixLift 2974601
  have htrace : WordTrace (prefixWord ++ tailWord_2974601) baseStart_2974601 baseEnd_2974601 := by
    simpa [prefixWord, tailWord_2974601, baseEnd_2974601] using wordTrace_append hprefix tailTrace_2974601
  have hstable : (prefixWord ++ tailWord_2974601).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974601).length < 2 ^ (prefixWord ++ tailWord_2974601).sum := by decide
  have hdescent : baseEnd_2974601 < baseStart_2974601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974628 : List Nat := [2, 3, 1, 2, 1, 2, 1, 5, 1, 3, 2]
def baseStart_2974628 : Nat := 118140960795 + 2974628 * 2 ^ 59
def prefixEnd_2974628 : Nat := 4983230072969 + 3 ^ 40 * 2974628 * 2
def baseEnd_2974628 : Nat := 1527413932322492987969941

theorem tailTrace_2974628 : CollatzResearch.WordTrace tailWord_2974628 prefixEnd_2974628 1527413932322492987969941 := by
  unfold tailWord_2974628
  simp only [CollatzResearch.WordTrace]
  refine ⟨54246798133719128430746269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72329064178292171240995025 54246798133719128430746269)
  ·
    refine ⟨20342549300144673161529851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54246798133719128430746269 20342549300144673161529851)
    ·
      refine ⟨30513823950217009742294777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20342549300144673161529851 30513823950217009742294777)
      ·
        refine ⟨22885367962662757306721083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30513823950217009742294777 22885367962662757306721083)
        ·
          refine ⟨34328051943994135960081625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22885367962662757306721083 34328051943994135960081625)
          ·
            refine ⟨25746038957995601970061219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 34328051943994135960081625 25746038957995601970061219)
            ·
              refine ⟨38619058436993402955091829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25746038957995601970061219 38619058436993402955091829)
              ·
                refine ⟨3620536728468131527039859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38619058436993402955091829 3620536728468131527039859)
                ·
                  refine ⟨5430805092702197290559789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620536728468131527039859 5430805092702197290559789)
                  ·
                    refine ⟨2036551909763323983959921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5430805092702197290559789 2036551909763323983959921)
                    ·
                      refine ⟨1527413932322492987969941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036551909763323983959921 1527413932322492987969941)
                      ·
                        rfl

theorem cell23_2974628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 2, 1, 5, 1, 3, 2].length) (baseStart_2974628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974628 prefixEnd_2974628 := by exact prefixLift 2974628
  have htrace : WordTrace (prefixWord ++ tailWord_2974628) baseStart_2974628 baseEnd_2974628 := by
    simpa [prefixWord, tailWord_2974628, baseEnd_2974628] using wordTrace_append hprefix tailTrace_2974628
  have hstable : (prefixWord ++ tailWord_2974628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974628).length < 2 ^ (prefixWord ++ tailWord_2974628).sum := by decide
  have hdescent : baseEnd_2974628 < baseStart_2974628 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974646 : List Nat := [5, 1, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_2974646 : Nat := 118140960795 + 2974646 * 2 ^ 59
def prefixEnd_2974646 : Nat := 4983230072969 + 3 ^ 40 * 2974646 * 2
def baseEnd_2974646 : Nat := 509141058324757972514953

theorem tailTrace_2974646 : CollatzResearch.WordTrace tailWord_2974646 prefixEnd_2974646 509141058324757972514953 := by
  unfold tailWord_2974646
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780890798835815370977987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72329501854248697290431861 6780890798835815370977987)
  ·
    refine ⟨10171336198253723056466981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6780890798835815370977987 10171336198253723056466981)
    ·
      refine ⟨1907125537172573073087559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10171336198253723056466981 1907125537172573073087559)
      ·
        refine ⟨2860688305758859609631339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1907125537172573073087559 2860688305758859609631339)
        ·
          refine ⟨4291032458638289414447009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2860688305758859609631339 4291032458638289414447009)
          ·
            refine ⟨3218274343978717060835257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4291032458638289414447009 3218274343978717060835257)
            ·
              refine ⟨2413705757984037795626443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218274343978717060835257 2413705757984037795626443)
              ·
                refine ⟨3620558636976056693439665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2413705757984037795626443 3620558636976056693439665)
                ·
                  refine ⟨2715418977732042520079749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620558636976056693439665 2715418977732042520079749)
                  ·
                    refine ⟨509141058324757972514953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2715418977732042520079749 509141058324757972514953)
                    ·
                      rfl

theorem cell23_2974646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_2974646 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974646 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974646 prefixEnd_2974646 := by exact prefixLift 2974646
  have htrace : WordTrace (prefixWord ++ tailWord_2974646) baseStart_2974646 baseEnd_2974646 := by
    simpa [prefixWord, tailWord_2974646, baseEnd_2974646] using wordTrace_append hprefix tailTrace_2974646
  have hstable : (prefixWord ++ tailWord_2974646).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974646).length < 2 ^ (prefixWord ++ tailWord_2974646).sum := by decide
  have hdescent : baseEnd_2974646 < baseStart_2974646 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974678 : List Nat := [5, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_2974678 : Nat := 118140960795 + 2974678 * 2 ^ 59
def prefixEnd_2974678 : Nat := 4983230072969 + 3 ^ 40 * 2974678 * 2
def baseEnd_2974678 : Nat := 1527439606355217792344711

theorem tailTrace_2974678 : CollatzResearch.WordTrace tailWord_2974678 prefixEnd_2974678 1527439606355217792344711 := by
  unfold tailWord_2974678
  simp only [CollatzResearch.WordTrace]
  refine ⟨6780963744828569712550793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 72330279944838076933875125 6780963744828569712550793)
  ·
    refine ⟨5085722808621427284413095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6780963744828569712550793 5085722808621427284413095)
    ·
      refine ⟨7628584212932140926619643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5085722808621427284413095 7628584212932140926619643)
      ·
        refine ⟨11442876319398211389929465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7628584212932140926619643 11442876319398211389929465)
        ·
          refine ⟨8582157239548658542447099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11442876319398211389929465 8582157239548658542447099)
          ·
            refine ⟨12873235859322987813670649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8582157239548658542447099 12873235859322987813670649)
            ·
              refine ⟨9654926894492240860252987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12873235859322987813670649 9654926894492240860252987)
              ·
                refine ⟨14482390341738361290379481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9654926894492240860252987 14482390341738361290379481)
                ·
                  refine ⟨10861792756303770967784611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14482390341738361290379481 10861792756303770967784611)
                  ·
                    refine ⟨16292689134455656451676917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10861792756303770967784611 16292689134455656451676917)
                    ·
                      refine ⟨1527439606355217792344711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16292689134455656451676917 1527439606355217792344711)
                      ·
                        rfl

theorem cell23_2974678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_2974678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974678 prefixEnd_2974678 := by exact prefixLift 2974678
  have htrace : WordTrace (prefixWord ++ tailWord_2974678) baseStart_2974678 baseEnd_2974678 := by
    simpa [prefixWord, tailWord_2974678, baseEnd_2974678] using wordTrace_append hprefix tailTrace_2974678
  have hstable : (prefixWord ++ tailWord_2974678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974678).length < 2 ^ (prefixWord ++ tailWord_2974678).sum := by decide
  have hdescent : baseEnd_2974678 < baseStart_2974678 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974691 : List Nat := [1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3]
def baseStart_2974691 : Nat := 118140960795 + 2974691 * 2 ^ 59
def prefixEnd_2974691 : Nat := 4983230072969 + 3 ^ 40 * 2974691 * 2
def baseEnd_2974691 : Nat := 1527446281603726241482151

theorem tailTrace_2974691 : CollatzResearch.WordTrace tailWord_2974691 prefixEnd_2974691 1527446281603726241482151 := by
  unfold tailWord_2974691
  simp only [CollatzResearch.WordTrace]
  refine ⟨108495894066210018621035927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72330596044140012414023951 108495894066210018621035927)
  ·
    refine ⟨162743841099315027931553891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108495894066210018621035927 162743841099315027931553891)
    ·
      refine ⟨244115761648972541897330837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162743841099315027931553891 244115761648972541897330837)
      ·
        refine ⟨11442926327295587901437383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 244115761648972541897330837 11442926327295587901437383)
        ·
          refine ⟨17164389490943381852156075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11442926327295587901437383 17164389490943381852156075)
          ·
            refine ⟨25746584236415072778234113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 17164389490943381852156075 25746584236415072778234113)
            ·
              refine ⟨19309938177311304583675585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25746584236415072778234113 19309938177311304583675585)
              ·
                refine ⟨14482453632983478437756689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19309938177311304583675585 14482453632983478437756689)
                ·
                  refine ⟨10861840224737608828317517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14482453632983478437756689 10861840224737608828317517)
                  ·
                    refine ⟨4073190084276603310619069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10861840224737608828317517 4073190084276603310619069)
                    ·
                      refine ⟨1527446281603726241482151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073190084276603310619069 1527446281603726241482151)
                      ·
                        rfl

theorem cell23_2974691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 2, 2, 2, 3, 3].length) (baseStart_2974691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974691 prefixEnd_2974691 := by exact prefixLift 2974691
  have htrace : WordTrace (prefixWord ++ tailWord_2974691) baseStart_2974691 baseEnd_2974691 := by
    simpa [prefixWord, tailWord_2974691, baseEnd_2974691] using wordTrace_append hprefix tailTrace_2974691
  have hstable : (prefixWord ++ tailWord_2974691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974691).length < 2 ^ (prefixWord ++ tailWord_2974691).sum := by decide
  have hdescent : baseEnd_2974691 < baseStart_2974691 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974698 : List Nat := [3, 1, 3, 1, 2, 3, 1, 4, 5]
def baseStart_2974698 : Nat := 118140960795 + 2974698 * 2 ^ 59
def prefixEnd_2974698 : Nat := 4983230072969 + 3 ^ 40 * 2974698 * 2
def baseEnd_2974698 : Nat := 169716652885367523788291

theorem tailTrace_2974698 : CollatzResearch.WordTrace tailWord_2974698 prefixEnd_2974698 169716652885367523788291 := by
  unfold tailWord_2974698
  simp only [CollatzResearch.WordTrace]
  refine ⟨27124037344296164704135187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72330766251456439211027165 27124037344296164704135187)
  ·
    refine ⟨40686056016444247056202781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27124037344296164704135187 40686056016444247056202781)
    ·
      refine ⟨15257271006166592646076043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40686056016444247056202781 15257271006166592646076043)
      ·
        refine ⟨22885906509249888969114065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15257271006166592646076043 22885906509249888969114065)
        ·
          refine ⟨17164429881937416726835549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22885906509249888969114065 17164429881937416726835549)
          ·
            refine ⟨6436661205726531272563331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17164429881937416726835549 6436661205726531272563331)
            ·
              refine ⟨9654991808589796908844997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436661205726531272563331 9654991808589796908844997)
              ·
                refine ⟨1810310964110586920408437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9654991808589796908844997 1810310964110586920408437)
                ·
                  refine ⟨169716652885367523788291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1810310964110586920408437 169716652885367523788291)
                  ·
                    rfl

theorem cell23_2974698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 4, 5].length) (baseStart_2974698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974698 prefixEnd_2974698 := by exact prefixLift 2974698
  have htrace : WordTrace (prefixWord ++ tailWord_2974698) baseStart_2974698 baseEnd_2974698 := by
    simpa [prefixWord, tailWord_2974698, baseEnd_2974698] using wordTrace_append hprefix tailTrace_2974698
  have hstable : (prefixWord ++ tailWord_2974698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974698).length < 2 ^ (prefixWord ++ tailWord_2974698).sum := by decide
  have hdescent : baseEnd_2974698 < baseStart_2974698 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974728 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 2, 5]
def baseStart_2974728 : Nat := 118140960795 + 2974728 * 2 ^ 59
def prefixEnd_2974728 : Nat := 4983230072969 + 3 ^ 40 * 2974728 * 2
def baseEnd_2974728 : Nat := 509155093462647532239827

theorem tailTrace_2974728 : CollatzResearch.WordTrace tailWord_2974728 prefixEnd_2974728 509155093462647532239827 := by
  unfold tailWord_2974728
  simp only [CollatzResearch.WordTrace]
  refine ⟨54248621783537986970066419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72331495711383982626755225 54248621783537986970066419)
  ·
    refine ⟨81372932675306980455099629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54248621783537986970066419 81372932675306980455099629)
    ·
      refine ⟨30514849753240117670662361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81372932675306980455099629 30514849753240117670662361)
      ·
        refine ⟨22886137314930088252996771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30514849753240117670662361 22886137314930088252996771)
        ·
          refine ⟨34329205972395132379495157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22886137314930088252996771 34329205972395132379495157)
          ·
            refine ⟨3218363059912043660577671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 34329205972395132379495157 3218363059912043660577671)
            ·
              refine ⟨4827544589868065490866507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3218363059912043660577671 4827544589868065490866507)
              ·
                refine ⟨7241316884802098236299761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4827544589868065490866507 7241316884802098236299761)
                ·
                  refine ⟨5430987663601573677224821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7241316884802098236299761 5430987663601573677224821)
                  ·
                    refine ⟨509155093462647532239827, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 5430987663601573677224821 509155093462647532239827)
                    ·
                      rfl

theorem cell23_2974728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 2, 5].length) (baseStart_2974728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974728 prefixEnd_2974728 := by exact prefixLift 2974728
  have htrace : WordTrace (prefixWord ++ tailWord_2974728) baseStart_2974728 baseEnd_2974728 := by
    simpa [prefixWord, tailWord_2974728, baseEnd_2974728] using wordTrace_append hprefix tailTrace_2974728
  have hstable : (prefixWord ++ tailWord_2974728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974728).length < 2 ^ (prefixWord ++ tailWord_2974728).sum := by decide
  have hdescent : baseEnd_2974728 < baseStart_2974728 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974731 : List Nat := [1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4]
def baseStart_2974731 : Nat := 118140960795 + 2974731 * 2 ^ 59
def prefixEnd_2974731 : Nat := 4983230072969 + 3 ^ 40 * 2974731 * 2
def baseEnd_2974731 : Nat := 1527466820829906084981967

theorem tailTrace_2974731 : CollatzResearch.WordTrace tailWord_2974731 prefixEnd_2974731 1527466820829906084981967 := by
  unfold tailWord_2974731
  simp only [CollatzResearch.WordTrace]
  refine ⟨108497352986065105452492047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72331568657376736968328031 108497352986065105452492047)
  ·
    refine ⟨162746029479097658178738071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108497352986065105452492047 162746029479097658178738071)
    ·
      refine ⟨244119044218646487268107107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162746029479097658178738071 244119044218646487268107107)
      ·
        refine ⟨366178566327969730902160661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244119044218646487268107107 366178566327969730902160661)
        ·
          refine ⟨17164620296623581136038781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 366178566327969730902160661 17164620296623581136038781)
          ·
            refine ⟨6436732611233842926014543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17164620296623581136038781 6436732611233842926014543)
            ·
              refine ⟨9655098916850764389021815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6436732611233842926014543 9655098916850764389021815)
              ·
                refine ⟨14482648375276146583532723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9655098916850764389021815 14482648375276146583532723)
                ·
                  refine ⟨21723972562914219875299085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14482648375276146583532723 21723972562914219875299085)
                  ·
                    refine ⟨8146489711092832453237157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21723972562914219875299085 8146489711092832453237157)
                    ·
                      refine ⟨1527466820829906084981967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8146489711092832453237157 1527466820829906084981967)
                      ·
                        rfl

theorem cell23_2974731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 3, 1, 1, 1, 3, 4].length) (baseStart_2974731 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974731 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974731 prefixEnd_2974731 := by exact prefixLift 2974731
  have htrace : WordTrace (prefixWord ++ tailWord_2974731) baseStart_2974731 baseEnd_2974731 := by
    simpa [prefixWord, tailWord_2974731, baseEnd_2974731] using wordTrace_append hprefix tailTrace_2974731
  have hstable : (prefixWord ++ tailWord_2974731).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974731).length < 2 ^ (prefixWord ++ tailWord_2974731).sum := by decide
  have hdescent : baseEnd_2974731 < baseStart_2974731 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974831 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 1, 6]
def baseStart_2974831 : Nat := 118140960795 + 2974831 * 2 ^ 59
def prefixEnd_2974831 : Nat := 4983230072969 + 3 ^ 40 * 2974831 * 2
def baseEnd_2974831 : Nat := 509172722965118564577169

theorem tailTrace_2974831 : CollatzResearch.WordTrace tailWord_2974831 prefixEnd_2974831 509172722965118564577169 := by
  unfold tailWord_2974831
  simp only [CollatzResearch.WordTrace]
  refine ⟨108501000285702822531132347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72334000190468548354088231 108501000285702822531132347)
  ·
    refine ⟨162751500428554233796698521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108501000285702822531132347 162751500428554233796698521)
    ·
      refine ⟨122063625321415675347523891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 162751500428554233796698521 122063625321415675347523891)
      ·
        refine ⟨183095437982123513021285837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122063625321415675347523891 183095437982123513021285837)
        ·
          refine ⟨68660789243296317382982189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 183095437982123513021285837 68660789243296317382982189)
          ·
            refine ⟨25747795966236119018618321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 68660789243296317382982189 25747795966236119018618321)
            ·
              refine ⟨19310846974677089263963741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25747795966236119018618321 19310846974677089263963741)
              ·
                refine ⟨7241567615503908473986403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19310846974677089263963741 7241567615503908473986403)
                ·
                  refine ⟨10862351423255862710979605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7241567615503908473986403 10862351423255862710979605)
                  ·
                    refine ⟨509172722965118564577169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 10862351423255862710979605 509172722965118564577169)
                    ·
                      rfl

theorem cell23_2974831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 6].length) (baseStart_2974831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974831 prefixEnd_2974831 := by exact prefixLift 2974831
  have htrace : WordTrace (prefixWord ++ tailWord_2974831) baseStart_2974831 baseEnd_2974831 := by
    simpa [prefixWord, tailWord_2974831, baseEnd_2974831] using wordTrace_append hprefix tailTrace_2974831
  have hstable : (prefixWord ++ tailWord_2974831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974831).length < 2 ^ (prefixWord ++ tailWord_2974831).sum := by decide
  have hdescent : baseEnd_2974831 < baseStart_2974831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974866 : List Nat := [3, 2, 3, 1, 1, 4, 2, 2, 1, 1, 3]
def baseStart_2974866 : Nat := 118140960795 + 2974866 * 2 ^ 59
def prefixEnd_2974866 : Nat := 4983230072969 + 3 ^ 40 * 2974866 * 2
def baseEnd_2974866 : Nat := 1527536140718263056793847

theorem tailTrace_2974866 : CollatzResearch.WordTrace tailWord_2974866 prefixEnd_2974866 1527536140718263056793847 := by
  unfold tailWord_2974866
  simp only [CollatzResearch.WordTrace]
  refine ⟨27125569210144005877164113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72334851227050682339104301 27125569210144005877164113)
  ·
    refine ⟨20344176907608004407873085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27125569210144005877164113 20344176907608004407873085)
    ·
      refine ⟨7629066340353001652952407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20344176907608004407873085 7629066340353001652952407)
      ·
        refine ⟨11443599510529502479428611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7629066340353001652952407 11443599510529502479428611)
        ·
          refine ⟨17165399265794253719142917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11443599510529502479428611 17165399265794253719142917)
          ·
            refine ⟨3218512362336422572339297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 17165399265794253719142917 3218512362336422572339297)
            ·
              refine ⟨2413884271752316929254473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3218512362336422572339297 2413884271752316929254473)
              ·
                refine ⟨1810413203814237696940855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2413884271752316929254473 1810413203814237696940855)
                ·
                  refine ⟨2715619805721356545411283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1810413203814237696940855 2715619805721356545411283)
                  ·
                    refine ⟨4073429708582034818116925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715619805721356545411283 4073429708582034818116925)
                    ·
                      refine ⟨1527536140718263056793847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073429708582034818116925 1527536140718263056793847)
                      ·
                        rfl

theorem cell23_2974866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 4, 2, 2, 1, 1, 3].length) (baseStart_2974866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974866 prefixEnd_2974866 := by exact prefixLift 2974866
  have htrace : WordTrace (prefixWord ++ tailWord_2974866) baseStart_2974866 baseEnd_2974866 := by
    simpa [prefixWord, tailWord_2974866, baseEnd_2974866] using wordTrace_append hprefix tailTrace_2974866
  have hstable : (prefixWord ++ tailWord_2974866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974866).length < 2 ^ (prefixWord ++ tailWord_2974866).sum := by decide
  have hdescent : baseEnd_2974866 < baseStart_2974866 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974922 : List Nat := [3, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3]
def baseStart_2974922 : Nat := 118140960795 + 2974922 * 2 ^ 59
def prefixEnd_2974922 : Nat := 4983230072969 + 3 ^ 40 * 2974922 * 2
def baseEnd_2974922 : Nat := 1527564895634914837693589

theorem tailTrace_2974922 : CollatzResearch.WordTrace tailWord_2974922 prefixEnd_2974922 1527564895634914837693589 := by
  unfold tailWord_2974922
  simp only [CollatzResearch.WordTrace]
  refine ⟨27126079832093286268173755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72336212885582096715130013 27126079832093286268173755)
  ·
    refine ⟨40689119748139929402260633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27126079832093286268173755 40689119748139929402260633)
    ·
      refine ⟨30516839811104947051695475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40689119748139929402260633 30516839811104947051695475)
      ·
        refine ⟨45775259716657420577543213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30516839811104947051695475 45775259716657420577543213)
        ·
          refine ⟨17165722393746532716578705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45775259716657420577543213 17165722393746532716578705)
          ·
            refine ⟨12874291795309899537434029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17165722393746532716578705 12874291795309899537434029)
            ·
              refine ⟨4827859423241212326537761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12874291795309899537434029 4827859423241212326537761)
              ·
                refine ⟨3620894567430909244903321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827859423241212326537761 3620894567430909244903321)
                ·
                  refine ⟨2715670925573181933677491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3620894567430909244903321 2715670925573181933677491)
                  ·
                    refine ⟨4073506388359772900516237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2715670925573181933677491 4073506388359772900516237)
                    ·
                      refine ⟨1527564895634914837693589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073506388359772900516237 1527564895634914837693589)
                      ·
                        rfl

theorem cell23_2974922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 2, 2, 1, 3].length) (baseStart_2974922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974922 prefixEnd_2974922 := by exact prefixLift 2974922
  have htrace : WordTrace (prefixWord ++ tailWord_2974922) baseStart_2974922 baseEnd_2974922 := by
    simpa [prefixWord, tailWord_2974922, baseEnd_2974922] using wordTrace_append hprefix tailTrace_2974922
  have hstable : (prefixWord ++ tailWord_2974922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974922).length < 2 ^ (prefixWord ++ tailWord_2974922).sum := by decide
  have hdescent : baseEnd_2974922 < baseStart_2974922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974928 : List Nat := [2, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2]
def baseStart_2974928 : Nat := 118140960795 + 2974928 * 2 ^ 59
def prefixEnd_2974928 : Nat := 4983230072969 + 3 ^ 40 * 2974928 * 2
def baseEnd_2974928 : Nat := 1527567976518841814218561

theorem tailTrace_2974928 : CollatzResearch.WordTrace tailWord_2974928 prefixEnd_2974928 1527567976518841814218561 := by
  unfold tailWord_2974928
  simp only [CollatzResearch.WordTrace]
  refine ⟨54252269083175704048706719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72336358777567605398275625 54252269083175704048706719)
  ·
    refine ⟨81378403624763556073060079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54252269083175704048706719 81378403624763556073060079)
    ·
      refine ⟨122067605437145334109590119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81378403624763556073060079 122067605437145334109590119)
      ·
        refine ⟨183101408155718001164385179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122067605437145334109590119 183101408155718001164385179)
        ·
          refine ⟨274652112233577001746577769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183101408155718001164385179 274652112233577001746577769)
          ·
            refine ⟨205989084175182751309933327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 274652112233577001746577769 205989084175182751309933327)
            ·
              refine ⟨308983626262774126964899991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205989084175182751309933327 308983626262774126964899991)
              ·
                refine ⟨463475439394161190447349987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308983626262774126964899991 463475439394161190447349987)
                ·
                  refine ⟨695213159091241785671024981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463475439394161190447349987 695213159091241785671024981)
                  ·
                    refine ⟨2036757302025122418958081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 695213159091241785671024981 2036757302025122418958081)
                    ·
                      refine ⟨1527567976518841814218561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036757302025122418958081 1527567976518841814218561)
                      ·
                        rfl

theorem cell23_2974928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 10, 2].length) (baseStart_2974928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974928 prefixEnd_2974928 := by exact prefixLift 2974928
  have htrace : WordTrace (prefixWord ++ tailWord_2974928) baseStart_2974928 baseEnd_2974928 := by
    simpa [prefixWord, tailWord_2974928, baseEnd_2974928] using wordTrace_append hprefix tailTrace_2974928
  have hstable : (prefixWord ++ tailWord_2974928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974928).length < 2 ^ (prefixWord ++ tailWord_2974928).sum := by decide
  have hdescent : baseEnd_2974928 < baseStart_2974928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974931 : List Nat := [1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5]
def baseStart_2974931 : Nat := 118140960795 + 2974931 * 2 ^ 59
def prefixEnd_2974931 : Nat := 4983230072969 + 3 ^ 40 * 2974931 * 2
def baseEnd_2974931 : Nat := 1527569516960805302481047

theorem tailTrace_2974931 : CollatzResearch.WordTrace tailWord_2974931 prefixEnd_2974931 1527569516960805302481047 := by
  unfold tailWord_2974931
  simp only [CollatzResearch.WordTrace]
  refine ⟨108504647585340539609772647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72336431723560359739848431 108504647585340539609772647)
  ·
    refine ⟨162756971378010809414658971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108504647585340539609772647 162756971378010809414658971)
    ·
      refine ⟨244135457067016214121988457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162756971378010809414658971 244135457067016214121988457)
      ·
        refine ⟨183101592800262160591491343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 244135457067016214121988457 183101592800262160591491343)
        ·
          refine ⟨274652389200393240887237015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183101592800262160591491343 274652389200393240887237015)
          ·
            refine ⟨411978583800589861330855523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274652389200393240887237015 411978583800589861330855523)
            ·
              refine ⟨617967875700884791996283285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 411978583800589861330855523 617967875700884791996283285)
              ·
                refine ⟨28967244173478974624825779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 617967875700884791996283285 28967244173478974624825779)
                ·
                  refine ⟨43450866260218461937238669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28967244173478974624825779 43450866260218461937238669)
                  ·
                    refine ⟨16294074847581923226464501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 43450866260218461937238669 16294074847581923226464501)
                    ·
                      refine ⟨1527569516960805302481047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16294074847581923226464501 1527569516960805302481047)
                      ·
                        rfl

theorem cell23_2974931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 6, 1, 3, 5].length) (baseStart_2974931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974931 prefixEnd_2974931 := by exact prefixLift 2974931
  have htrace : WordTrace (prefixWord ++ tailWord_2974931) baseStart_2974931 baseEnd_2974931 := by
    simpa [prefixWord, tailWord_2974931, baseEnd_2974931] using wordTrace_append hprefix tailTrace_2974931
  have hstable : (prefixWord ++ tailWord_2974931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974931).length < 2 ^ (prefixWord ++ tailWord_2974931).sum := by decide
  have hdescent : baseEnd_2974931 < baseStart_2974931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974948 : List Nat := [2, 3, 1, 1, 1, 2, 2, 2, 2, 4, 3]
def baseStart_2974948 : Nat := 118140960795 + 2974948 * 2 ^ 59
def prefixEnd_2974948 : Nat := 4983230072969 + 3 ^ 40 * 2974948 * 2
def baseEnd_2974948 : Nat := 1527578246131931735968469

theorem tailTrace_2974948 : CollatzResearch.WordTrace tailWord_2974948 prefixEnd_2974948 1527578246131931735968469 := by
  unfold tailWord_2974948
  simp only [CollatzResearch.WordTrace]
  refine ⟨54252633813139475756570749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72336845084185967675427665 54252633813139475756570749)
  ·
    refine ⟨20344737679927303408714031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 54252633813139475756570749 20344737679927303408714031)
    ·
      refine ⟨30517106519890955113071047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20344737679927303408714031 30517106519890955113071047)
      ·
        refine ⟨45775659779836432669606571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30517106519890955113071047 45775659779836432669606571)
        ·
          refine ⟨68663489669754649004409857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45775659779836432669606571 68663489669754649004409857)
          ·
            refine ⟨51497617252315986753307393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68663489669754649004409857 51497617252315986753307393)
            ·
              refine ⟨38623212939236990064980545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51497617252315986753307393 38623212939236990064980545)
              ·
                refine ⟨28967409704427742548735409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38623212939236990064980545 28967409704427742548735409)
                ·
                  refine ⟨21725557278320806911551557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28967409704427742548735409 21725557278320806911551557)
                  ·
                    refine ⟨4073541989685151295915917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21725557278320806911551557 4073541989685151295915917)
                    ·
                      refine ⟨1527578246131931735968469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073541989685151295915917 1527578246131931735968469)
                      ·
                        rfl

theorem cell23_2974948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 2, 2, 4, 3].length) (baseStart_2974948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974948 prefixEnd_2974948 := by exact prefixLift 2974948
  have htrace : WordTrace (prefixWord ++ tailWord_2974948) baseStart_2974948 baseEnd_2974948 := by
    simpa [prefixWord, tailWord_2974948, baseEnd_2974948] using wordTrace_append hprefix tailTrace_2974948
  have hstable : (prefixWord ++ tailWord_2974948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974948).length < 2 ^ (prefixWord ++ tailWord_2974948).sum := by decide
  have hdescent : baseEnd_2974948 < baseStart_2974948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974949 : List Nat := [1, 3, 1, 4, 3, 1, 2, 2, 1, 3, 2]
def baseStart_2974949 : Nat := 118140960795 + 2974949 * 2 ^ 59
def prefixEnd_2974949 : Nat := 4983230072969 + 3 ^ 40 * 2974949 * 2
def baseEnd_2974949 : Nat := 1527578759612586232055965

theorem tailTrace_2974949 : CollatzResearch.WordTrace tailWord_2974949 prefixEnd_2974949 1527578759612586232055965 := by
  unfold tailWord_2974949
  simp only [CollatzResearch.WordTrace]
  refine ⟨108505304099275328683927901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72336869399516885789285267 108505304099275328683927901)
  ·
    refine ⟨40689489037228248256472963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108505304099275328683927901 40689489037228248256472963)
    ·
      refine ⟨61034233555842372384709445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40689489037228248256472963 61034233555842372384709445)
      ·
        refine ⟨11443918791720444822133021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 61034233555842372384709445 11443918791720444822133021)
        ·
          refine ⟨4291469546895166808299883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11443918791720444822133021 4291469546895166808299883)
          ·
            refine ⟨6437204320342750212449825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291469546895166808299883 6437204320342750212449825)
            ·
              refine ⟨4827903240257062659337369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6437204320342750212449825 4827903240257062659337369)
              ·
                refine ⟨3620927430192796994503027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4827903240257062659337369 3620927430192796994503027)
                ·
                  refine ⟨5431391145289195491754541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3620927430192796994503027 5431391145289195491754541)
                  ·
                    refine ⟨2036771679483448309407953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5431391145289195491754541 2036771679483448309407953)
                    ·
                      refine ⟨1527578759612586232055965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036771679483448309407953 1527578759612586232055965)
                      ·
                        rfl

theorem cell23_2974949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_2974949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974949 prefixEnd_2974949 := by exact prefixLift 2974949
  have htrace : WordTrace (prefixWord ++ tailWord_2974949) baseStart_2974949 baseEnd_2974949 := by
    simpa [prefixWord, tailWord_2974949, baseEnd_2974949] using wordTrace_append hprefix tailTrace_2974949
  have hstable : (prefixWord ++ tailWord_2974949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974949).length < 2 ^ (prefixWord ++ tailWord_2974949).sum := by decide
  have hdescent : baseEnd_2974949 < baseStart_2974949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974958 : List Nat := [4, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2974958 : Nat := 118140960795 + 2974958 * 2 ^ 59
def prefixEnd_2974958 : Nat := 4983230072969 + 3 ^ 40 * 2974958 * 2
def baseEnd_2974958 : Nat := 1527583380938476696843423

theorem tailTrace_2974958 : CollatzResearch.WordTrace tailWord_2974958 prefixEnd_2974958 1527583380938476696843423 := by
  unfold tailWord_2974958
  simp only [CollatzResearch.WordTrace]
  refine ⟨13563204044530340402625691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 72337088237495148814003685 13563204044530340402625691)
  ·
    refine ⟨20344806066795510603938537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13563204044530340402625691 20344806066795510603938537)
    ·
      refine ⟨15258604550096632952953903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20344806066795510603938537 15258604550096632952953903)
      ·
        refine ⟨22887906825144949429430855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15258604550096632952953903 22887906825144949429430855)
        ·
          refine ⟨34331860237717424144146283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22887906825144949429430855 34331860237717424144146283)
          ·
            refine ⟨51497790356576136216219425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34331860237717424144146283 51497790356576136216219425)
            ·
              refine ⟨38623342767432102162164569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51497790356576136216219425 38623342767432102162164569)
              ·
                refine ⟨28967507075574076621623427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38623342767432102162164569 28967507075574076621623427)
                ·
                  refine ⟨43451260613361114932435141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28967507075574076621623427 43451260613361114932435141)
                  ·
                    refine ⟨8147111365005209049831589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43451260613361114932435141 8147111365005209049831589)
                    ·
                      refine ⟨1527583380938476696843423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8147111365005209049831589 1527583380938476696843423)
                      ·
                        rfl

theorem cell23_2974958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2974958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974958 prefixEnd_2974958 := by exact prefixLift 2974958
  have htrace : WordTrace (prefixWord ++ tailWord_2974958) baseStart_2974958 baseEnd_2974958 := by
    simpa [prefixWord, tailWord_2974958, baseEnd_2974958] using wordTrace_append hprefix tailTrace_2974958
  have hstable : (prefixWord ++ tailWord_2974958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974958).length < 2 ^ (prefixWord ++ tailWord_2974958).sum := by decide
  have hdescent : baseEnd_2974958 < baseStart_2974958 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2974971 : List Nat := [1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6]
def baseStart_2974971 : Nat := 118140960795 + 2974971 * 2 ^ 59
def prefixEnd_2974971 : Nat := 4983230072969 + 3 ^ 40 * 2974971 * 2
def baseEnd_2974971 : Nat := 1527590056186985145980863

theorem tailTrace_2974971 : CollatzResearch.WordTrace tailWord_2974971 prefixEnd_2974971 1527590056186985145980863 := by
  unfold tailWord_2974971
  simp only [CollatzResearch.WordTrace]
  refine ⟨108506106505195626441228767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72337404336797084294152511 108506106505195626441228767)
  ·
    refine ⟨162759159757793439661843151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 108506106505195626441228767 162759159757793439661843151)
    ·
      refine ⟨244138739636690159492764727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 162759159757793439661843151 244138739636690159492764727)
      ·
        refine ⟨366208109455035239239147091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 244138739636690159492764727 366208109455035239239147091)
        ·
          refine ⟨549312164182552858858720637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 366208109455035239239147091 549312164182552858858720637)
          ·
            refine ⟨205992061568457322072020239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 549312164182552858858720637 205992061568457322072020239)
            ·
              refine ⟨308988092352685983108030359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 205992061568457322072020239 308988092352685983108030359)
              ·
                refine ⟨463482138529028974662045539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 308988092352685983108030359 463482138529028974662045539)
                ·
                  refine ⟨695223207793543461993068309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 463482138529028974662045539 695223207793543461993068309)
                  ·
                    refine ⟨32588587865322349780925077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 695223207793543461993068309 32588587865322349780925077)
                    ·
                      refine ⟨1527590056186985145980863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 32588587865322349780925077 1527590056186985145980863)
                      ·
                        rfl

theorem cell23_2974971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 6, 6].length) (baseStart_2974971 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2974971 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2974971 prefixEnd_2974971 := by exact prefixLift 2974971
  have htrace : WordTrace (prefixWord ++ tailWord_2974971) baseStart_2974971 baseEnd_2974971 := by
    simpa [prefixWord, tailWord_2974971, baseEnd_2974971] using wordTrace_append hprefix tailTrace_2974971
  have hstable : (prefixWord ++ tailWord_2974971).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2974971).length < 2 ^ (prefixWord ++ tailWord_2974971).sum := by decide
  have hdescent : baseEnd_2974971 < baseStart_2974971 := by decide
  rcases family_descends (prefixWord ++ tailWord_2974971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975046 : List Nat := [6, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3]
def baseStart_2975046 : Nat := 118140960795 + 2975046 * 2 ^ 59
def prefixEnd_2975046 : Nat := 4983230072969 + 3 ^ 40 * 2975046 * 2
def baseEnd_2975046 : Nat := 1527628567236072352543019

theorem tailTrace_2975046 : CollatzResearch.WordTrace tailWord_2975046 prefixEnd_2975046 1527628567236072352543019 := by
  unfold tailWord_2975046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3390901311872622320319031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 72339227986615942833472661 3390901311872622320319031)
  ·
    refine ⟨5086351967808933480478547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3390901311872622320319031 5086351967808933480478547)
    ·
      refine ⟨7629527951713400220717821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5086351967808933480478547 7629527951713400220717821)
      ·
        refine ⟨2861072981892525082769183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7629527951713400220717821 2861072981892525082769183)
        ·
          refine ⟨4291609472838787624153775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2861072981892525082769183 4291609472838787624153775)
          ·
            refine ⟨6437414209258181436230663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4291609472838787624153775 6437414209258181436230663)
            ·
              refine ⟨9656121313887272154345995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437414209258181436230663 9656121313887272154345995)
              ·
                refine ⟨14484181970830908231518993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656121313887272154345995 14484181970830908231518993)
                ·
                  refine ⟨10863136478123181173639245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14484181970830908231518993 10863136478123181173639245)
                  ·
                    refine ⟨4073676179296192940114717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10863136478123181173639245 4073676179296192940114717)
                    ·
                      refine ⟨1527628567236072352543019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073676179296192940114717 1527628567236072352543019)
                      ·
                        rfl

theorem cell23_2975046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_2975046 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975046 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975046 prefixEnd_2975046 := by exact prefixLift 2975046
  have htrace : WordTrace (prefixWord ++ tailWord_2975046) baseStart_2975046 baseEnd_2975046 := by
    simpa [prefixWord, tailWord_2975046, baseEnd_2975046] using wordTrace_append hprefix tailTrace_2975046
  have hstable : (prefixWord ++ tailWord_2975046).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975046).length < 2 ^ (prefixWord ++ tailWord_2975046).sum := by decide
  have hdescent : baseEnd_2975046 < baseStart_2975046 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975048 : List Nat := [2, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4]
def baseStart_2975048 : Nat := 118140960795 + 2975048 * 2 ^ 59
def prefixEnd_2975048 : Nat := 4983230072969 + 3 ^ 40 * 2975048 * 2
def baseEnd_2975048 : Nat := 1527629594197381344718009

theorem tailTrace_2975048 : CollatzResearch.WordTrace tailWord_2975048 prefixEnd_2975048 1527629594197381344718009 := by
  unfold tailWord_2975048
  simp only [CollatzResearch.WordTrace]
  refine ⟨54254457462958334295890899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72339276617277779061187865 54254457462958334295890899)
  ·
    refine ⟨81381686194437501443836349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54254457462958334295890899 81381686194437501443836349)
    ·
      refine ⟨30518132322914063041438631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81381686194437501443836349 30518132322914063041438631)
      ·
        refine ⟨45777198484371094562157947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30518132322914063041438631 45777198484371094562157947)
        ·
          refine ⟨68665797726556641843236921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45777198484371094562157947 68665797726556641843236921)
          ·
            refine ⟨51499348294917481382427691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68665797726556641843236921 51499348294917481382427691)
            ·
              refine ⟨77249022442376222073641537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51499348294917481382427691 77249022442376222073641537)
              ·
                refine ⟨57936766831782166555231153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77249022442376222073641537 57936766831782166555231153)
                ·
                  refine ⟨43452575123836624916423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57936766831782166555231153 43452575123836624916423365)
                  ·
                    refine ⟨8147357835719367171829381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 43452575123836624916423365 8147357835719367171829381)
                    ·
                      refine ⟨1527629594197381344718009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8147357835719367171829381 1527629594197381344718009)
                      ·
                        rfl

theorem cell23_2975048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_2975048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975048 prefixEnd_2975048 := by exact prefixLift 2975048
  have htrace : WordTrace (prefixWord ++ tailWord_2975048) baseStart_2975048 baseEnd_2975048 := by
    simpa [prefixWord, tailWord_2975048, baseEnd_2975048] using wordTrace_append hprefix tailTrace_2975048
  have hstable : (prefixWord ++ tailWord_2975048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975048).length < 2 ^ (prefixWord ++ tailWord_2975048).sum := by decide
  have hdescent : baseEnd_2975048 < baseStart_2975048 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975052 : List Nat := [2, 2, 1, 3, 2, 3, 1, 1, 2, 4, 2]
def baseStart_2975052 : Nat := 118140960795 + 2975052 * 2 ^ 59
def prefixEnd_2975052 : Nat := 4983230072969 + 3 ^ 40 * 2975052 * 2
def baseEnd_2975052 : Nat := 1527631648119999329067991

theorem tailTrace_2975052 : CollatzResearch.WordTrace tailWord_2975052 prefixEnd_2975052 1527631648119999329067991 := by
  unfold tailWord_2975052
  simp only [CollatzResearch.WordTrace]
  refine ⟨54254530408951088637463705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72339373878601451516618273 54254530408951088637463705)
  ·
    refine ⟨40690897806713316478097779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54254530408951088637463705 40690897806713316478097779)
    ·
      refine ⟨61036346710069974717146669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40690897806713316478097779 61036346710069974717146669)
      ·
        refine ⟨22888630016276240518930001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 61036346710069974717146669 22888630016276240518930001)
        ·
          refine ⟨17166472512207180389197501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22888630016276240518930001 17166472512207180389197501)
          ·
            refine ⟨6437427192077692645949063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 17166472512207180389197501 6437427192077692645949063)
            ·
              refine ⟨9656140788116538968923595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6437427192077692645949063 9656140788116538968923595)
              ·
                refine ⟨14484211182174808453385393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9656140788116538968923595 14484211182174808453385393)
                ·
                  refine ⟨10863158386631106340039045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14484211182174808453385393 10863158386631106340039045)
                  ·
                    refine ⟨2036842197493332438757321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10863158386631106340039045 2036842197493332438757321)
                    ·
                      refine ⟨1527631648119999329067991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036842197493332438757321 1527631648119999329067991)
                      ·
                        rfl

theorem cell23_2975052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 2, 4, 2].length) (baseStart_2975052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975052 prefixEnd_2975052 := by exact prefixLift 2975052
  have htrace : WordTrace (prefixWord ++ tailWord_2975052) baseStart_2975052 baseEnd_2975052 := by
    simpa [prefixWord, tailWord_2975052, baseEnd_2975052] using wordTrace_append hprefix tailTrace_2975052
  have hstable : (prefixWord ++ tailWord_2975052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975052).length < 2 ^ (prefixWord ++ tailWord_2975052).sum := by decide
  have hdescent : baseEnd_2975052 < baseStart_2975052 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975058 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 10]
def baseStart_2975058 : Nat := 118140960795 + 2975058 * 2 ^ 59
def prefixEnd_2975058 : Nat := 4983230072969 + 3 ^ 40 * 2975058 * 2
def baseEnd_2975058 : Nat := 169737192111547367288107

theorem tailTrace_2975058 : CollatzResearch.WordTrace tailWord_2975058 prefixEnd_2975058 169737192111547367288107 := by
  unfold tailWord_2975058
  simp only [CollatzResearch.WordTrace]
  refine ⟨27127319913970110074911457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72339519770586960199763885 27127319913970110074911457)
  ·
    refine ⟨20345489935477582556183593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 27127319913970110074911457 20345489935477582556183593)
    ·
      refine ⟨15259117451608186917137695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20345489935477582556183593 15259117451608186917137695)
      ·
        refine ⟨22888676177412280375706543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15259117451608186917137695 22888676177412280375706543)
        ·
          refine ⟨34333014266118420563559815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22888676177412280375706543 34333014266118420563559815)
          ·
            refine ⟨51499521399177630845339723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 34333014266118420563559815 51499521399177630845339723)
            ·
              refine ⟨77249282098766446268009585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 51499521399177630845339723 77249282098766446268009585)
              ·
                refine ⟨57936961574074834701007189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 77249282098766446268009585 57936961574074834701007189)
                ·
                  refine ⟨169737192111547367288107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 57936961574074834701007189 169737192111547367288107)
                  ·
                    rfl

theorem cell23_2975058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 10].length) (baseStart_2975058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975058 prefixEnd_2975058 := by exact prefixLift 2975058
  have htrace : WordTrace (prefixWord ++ tailWord_2975058) baseStart_2975058 baseEnd_2975058 := by
    simpa [prefixWord, tailWord_2975058, baseEnd_2975058] using wordTrace_append hprefix tailTrace_2975058
  have hstable : (prefixWord ++ tailWord_2975058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975058).length < 2 ^ (prefixWord ++ tailWord_2975058).sum := by decide
  have hdescent : baseEnd_2975058 < baseStart_2975058 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975072 : List Nat := [2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3]
def baseStart_2975072 : Nat := 118140960795 + 2975072 * 2 ^ 59
def prefixEnd_2975072 : Nat := 4983230072969 + 3 ^ 40 * 2975072 * 2
def baseEnd_2975072 : Nat := 1527641917733089250817899

theorem tailTrace_2975072 : CollatzResearch.WordTrace tailWord_2975072 prefixEnd_2975072 1527641917733089250817899 := by
  unfold tailWord_2975072
  simp only [CollatzResearch.WordTrace]
  refine ⟨54254895138914860345327735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72339860185219813793770313 54254895138914860345327735)
  ·
    refine ⟨81382342708372290517991603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54254895138914860345327735 81382342708372290517991603)
    ·
      refine ⟨122073514062558435776987405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81382342708372290517991603 122073514062558435776987405)
      ·
        refine ⟨45777567773459413416370277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 122073514062558435776987405 45777567773459413416370277)
        ·
          refine ⟨8583293957523640015569427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45777567773459413416370277 8583293957523640015569427)
          ·
            refine ⟨12874940936285460023354141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8583293957523640015569427 12874940936285460023354141)
            ·
              refine ⟨4828102851107047508757803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12874940936285460023354141 4828102851107047508757803)
              ·
                refine ⟨7242154276660571263136705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4828102851107047508757803 7242154276660571263136705)
                ·
                  refine ⟨5431615707495428447352529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7242154276660571263136705 5431615707495428447352529)
                  ·
                    refine ⟨4073711780621571335514397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5431615707495428447352529 4073711780621571335514397)
                    ·
                      refine ⟨1527641917733089250817899, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073711780621571335514397 1527641917733089250817899)
                      ·
                        rfl

theorem cell23_2975072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 3].length) (baseStart_2975072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975072 prefixEnd_2975072 := by exact prefixLift 2975072
  have htrace : WordTrace (prefixWord ++ tailWord_2975072) baseStart_2975072 baseEnd_2975072 := by
    simpa [prefixWord, tailWord_2975072, baseEnd_2975072] using wordTrace_append hprefix tailTrace_2975072
  have hstable : (prefixWord ++ tailWord_2975072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975072).length < 2 ^ (prefixWord ++ tailWord_2975072).sum := by decide
  have hdescent : baseEnd_2975072 < baseStart_2975072 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975098 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5]
def baseStart_2975098 : Nat := 118140960795 + 2975098 * 2 ^ 59
def prefixEnd_2975098 : Nat := 4983230072969 + 3 ^ 40 * 2975098 * 2
def baseEnd_2975098 : Nat := 1527655268230106149092779

theorem tailTrace_2975098 : CollatzResearch.WordTrace tailWord_2975098 prefixEnd_2975098 1527655268230106149092779 := by
  unfold tailWord_2975098
  simp only [CollatzResearch.WordTrace]
  refine ⟨27127684643933881782775487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 72340492383823684754067965 27127684643933881782775487)
  ·
    refine ⟨40691526965900822674163231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 27127684643933881782775487 40691526965900822674163231)
    ·
      refine ⟨61037290448851234011244847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40691526965900822674163231 61037290448851234011244847)
      ·
        refine ⟨91555935673276851016867271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61037290448851234011244847 91555935673276851016867271)
        ·
          refine ⟨137333903509915276525300907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91555935673276851016867271 137333903509915276525300907)
          ·
            refine ⟨206000855264872914787951361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137333903509915276525300907 206000855264872914787951361)
            ·
              refine ⟨154500641448654686090963521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 206000855264872914787951361 154500641448654686090963521)
              ·
                refine ⟨115875481086491014568222641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 154500641448654686090963521 115875481086491014568222641)
                ·
                  refine ⟨86906610814868260926166981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 115875481086491014568222641 86906610814868260926166981)
                  ·
                    refine ⟨16294989527787798923656309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 86906610814868260926166981 16294989527787798923656309)
                    ·
                      refine ⟨1527655268230106149092779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 16294989527787798923656309 1527655268230106149092779)
                      ·
                        rfl

theorem cell23_2975098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 2, 4, 5].length) (baseStart_2975098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975098 prefixEnd_2975098 := by exact prefixLift 2975098
  have htrace : WordTrace (prefixWord ++ tailWord_2975098) baseStart_2975098 baseEnd_2975098 := by
    simpa [prefixWord, tailWord_2975098, baseEnd_2975098] using wordTrace_append hprefix tailTrace_2975098
  have hstable : (prefixWord ++ tailWord_2975098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975098).length < 2 ^ (prefixWord ++ tailWord_2975098).sum := by decide
  have hdescent : baseEnd_2975098 < baseStart_2975098 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975112 : List Nat := [2, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2]
def baseStart_2975112 : Nat := 118140960795 + 2975112 * 2 ^ 59
def prefixEnd_2975112 : Nat := 4983230072969 + 3 ^ 40 * 2975112 * 2
def baseEnd_2975112 : Nat := 1527662456959269094317715

theorem tailTrace_2975112 : CollatzResearch.WordTrace tailWord_2975112 prefixEnd_2975112 1527662456959269094317715 := by
  unfold tailWord_2975112
  simp only [CollatzResearch.WordTrace]
  refine ⟨54255624598842403761055795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72340832798456538348074393 54255624598842403761055795)
  ·
    refine ⟨81383436898263605641583693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 54255624598842403761055795 81383436898263605641583693)
    ·
      refine ⟨30518788836848852115593885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 81383436898263605641583693 30518788836848852115593885)
      ·
        refine ⟨11444545813818319543347707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30518788836848852115593885 11444545813818319543347707)
        ·
          refine ⟨17166818720727479315021561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11444545813818319543347707 17166818720727479315021561)
          ·
            refine ⟨12875114040545609486266171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 17166818720727479315021561 12875114040545609486266171)
            ·
              refine ⟨19312671060818414229399257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12875114040545609486266171 19312671060818414229399257)
              ·
                refine ⟨14484503295613810672049443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19312671060818414229399257 14484503295613810672049443)
                ·
                  refine ⟨21726754943420716008074165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14484503295613810672049443 21726754943420716008074165)
                  ·
                    refine ⟨2036883275945692125756953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21726754943420716008074165 2036883275945692125756953)
                    ·
                      refine ⟨1527662456959269094317715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2036883275945692125756953 1527662456959269094317715)
                      ·
                        rfl

theorem cell23_2975112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 2, 1, 5, 2].length) (baseStart_2975112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975112 prefixEnd_2975112 := by exact prefixLift 2975112
  have htrace : WordTrace (prefixWord ++ tailWord_2975112) baseStart_2975112 baseEnd_2975112 := by
    simpa [prefixWord, tailWord_2975112, baseEnd_2975112] using wordTrace_append hprefix tailTrace_2975112
  have hstable : (prefixWord ++ tailWord_2975112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975112).length < 2 ^ (prefixWord ++ tailWord_2975112).sum := by decide
  have hdescent : baseEnd_2975112 < baseStart_2975112 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975125 : List Nat := [1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 4]
def baseStart_2975125 : Nat := 118140960795 + 2975125 * 2 ^ 59
def prefixEnd_2975125 : Nat := 4983230072969 + 3 ^ 40 * 2975125 * 2
def baseEnd_2975125 : Nat := 1527669132207777543455155

theorem tailTrace_2975125 : CollatzResearch.WordTrace tailWord_2975125 prefixEnd_2975125 1527669132207777543455155 := by
  unfold tailWord_2975125
  simp only [CollatzResearch.WordTrace]
  refine ⟨108511723346637710742334829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72341148897758473828223219 108511723346637710742334829)
  ·
    refine ⟨40691896254989141528375561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 108511723346637710742334829 40691896254989141528375561)
    ·
      refine ⟨30518922191241856146281671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40691896254989141528375561 30518922191241856146281671)
      ·
        refine ⟨45778383286862784219422507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30518922191241856146281671 45778383286862784219422507)
        ·
          refine ⟨68667574930294176329133761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45778383286862784219422507 68667574930294176329133761)
          ·
            refine ⟨51500681197720632246850321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 68667574930294176329133761 51500681197720632246850321)
            ·
              refine ⟨38625510898290474185137741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 51500681197720632246850321 38625510898290474185137741)
              ·
                refine ⟨14484566586858927819426653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38625510898290474185137741 14484566586858927819426653)
                ·
                  refine ⟨5431712470072097932284995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14484566586858927819426653 5431712470072097932284995)
                  ·
                    refine ⟨8147568705108146898427493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5431712470072097932284995 8147568705108146898427493)
                    ·
                      refine ⟨1527669132207777543455155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 8147568705108146898427493 1527669132207777543455155)
                      ·
                        rfl

theorem cell23_2975125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_2975125 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975125 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975125 prefixEnd_2975125 := by exact prefixLift 2975125
  have htrace : WordTrace (prefixWord ++ tailWord_2975125) baseStart_2975125 baseEnd_2975125 := by
    simpa [prefixWord, tailWord_2975125, baseEnd_2975125] using wordTrace_append hprefix tailTrace_2975125
  have hstable : (prefixWord ++ tailWord_2975125).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975125).length < 2 ^ (prefixWord ++ tailWord_2975125).sum := by decide
  have hdescent : baseEnd_2975125 < baseStart_2975125 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975145 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3]
def baseStart_2975145 : Nat := 118140960795 + 2975145 * 2 ^ 59
def prefixEnd_2975145 : Nat := 4983230072969 + 3 ^ 40 * 2975145 * 2
def baseEnd_2975145 : Nat := 1527679401820867465205063

theorem tailTrace_2975145 : CollatzResearch.WordTrace tailWord_2975145 prefixEnd_2975145 1527679401820867465205063 := by
  unfold tailWord_2975145
  simp only [CollatzResearch.WordTrace]
  refine ⟨108512452806565254158062889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 72341635204376836105375259 108512452806565254158062889)
  ·
    refine ⟨81384339604923940618547167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 108512452806565254158062889 81384339604923940618547167)
    ·
      refine ⟨122076509407385910927820751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 81384339604923940618547167 122076509407385910927820751)
      ·
        refine ⟨183114764111078866391731127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 122076509407385910927820751 183114764111078866391731127)
        ·
          refine ⟨274672146166618299587596691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 183114764111078866391731127 274672146166618299587596691)
          ·
            refine ⟨412008219249927449381395037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 274672146166618299587596691 412008219249927449381395037)
            ·
              refine ⟨154503082218722793518023139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 412008219249927449381395037 154503082218722793518023139)
              ·
                refine ⟨231754623328084190277034709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 154503082218722793518023139 231754623328084190277034709)
                ·
                  refine ⟨5431748984251973209618001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 231754623328084190277034709 5431748984251973209618001)
                  ·
                    refine ⟨4073811738188979907213501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5431748984251973209618001 4073811738188979907213501)
                    ·
                      refine ⟨1527679401820867465205063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4073811738188979907213501 1527679401820867465205063)
                      ·
                        rfl

theorem cell23_2975145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_2975145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975145 prefixEnd_2975145 := by exact prefixLift 2975145
  have htrace : WordTrace (prefixWord ++ tailWord_2975145) baseStart_2975145 baseEnd_2975145 := by
    simpa [prefixWord, tailWord_2975145, baseEnd_2975145] using wordTrace_append hprefix tailTrace_2975145
  have hstable : (prefixWord ++ tailWord_2975145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975145).length < 2 ^ (prefixWord ++ tailWord_2975145).sum := by decide
  have hdescent : baseEnd_2975145 < baseStart_2975145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2975148 : List Nat := [2, 2, 1, 1, 1, 1, 15]
def baseStart_2975148 : Nat := 118140960795 + 2975148 * 2 ^ 59
def prefixEnd_2975148 : Nat := 4983230072969 + 3 ^ 40 * 2975148 * 2
def baseEnd_2975148 : Nat := 18860258546454703129229

theorem tailTrace_2975148 : CollatzResearch.WordTrace tailWord_2975148 prefixEnd_2975148 18860258546454703129229 := by
  unfold tailWord_2975148
  simp only [CollatzResearch.WordTrace]
  refine ⟨54256281112777192835211049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 72341708150369590446948065 54256281112777192835211049)
  ·
    refine ⟨40692210834582894626408287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 54256281112777192835211049 40692210834582894626408287)
    ·
      refine ⟨61038316251874341939612431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40692210834582894626408287 61038316251874341939612431)
      ·
        refine ⟨91557474377811512909418647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 61038316251874341939612431 91557474377811512909418647)
        ·
          refine ⟨137336211566717269364127971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 91557474377811512909418647 137336211566717269364127971)
          ·
            refine ⟨206004317350075904046191957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 137336211566717269364127971 206004317350075904046191957)
            ·
              refine ⟨18860258546454703129229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 15 206004317350075904046191957 18860258546454703129229)
              ·
                rfl

theorem cell23_2975148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 15].length) (baseStart_2975148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2975148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2975148 prefixEnd_2975148 := by exact prefixLift 2975148
  have htrace : WordTrace (prefixWord ++ tailWord_2975148) baseStart_2975148 baseEnd_2975148 := by
    simpa [prefixWord, tailWord_2975148, baseEnd_2975148] using wordTrace_append hprefix tailTrace_2975148
  have hstable : (prefixWord ++ tailWord_2975148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2975148).length < 2 ^ (prefixWord ++ tailWord_2975148).sum := by decide
  have hdescent : baseEnd_2975148 < baseStart_2975148 := by decide
  rcases family_descends (prefixWord ++ tailWord_2975148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
