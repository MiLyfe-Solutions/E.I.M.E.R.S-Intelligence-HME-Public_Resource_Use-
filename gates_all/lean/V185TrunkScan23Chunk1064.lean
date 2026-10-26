import V185TrunkScan23Chunk1063

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6298748 : List Nat := [2, 2, 2, 1, 1, 3, 1, 5, 6]
def baseStart_6298748 : Nat := 118140960795 + 6298748 * 2 ^ 59
def prefixEnd_6298748 : Nat := 4983230072969 + 3 ^ 40 * 6298748 * 2
def baseEnd_6298748 : Nat := 359365027282891928131399

theorem tailTrace_6298748 : CollatzResearch.WordTrace tailWord_6298748 prefixEnd_6298748 359365027282891928131399 := by
  unfold tailWord_6298748
  simp only [CollatzResearch.WordTrace]
  refine ⟨114867106492359605679716449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153156141989812807572955265 114867106492359605679716449)
  ·
    refine ⟨86150329869269704259787337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114867106492359605679716449 86150329869269704259787337)
    ·
      refine ⟨64612747401952278194840503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86150329869269704259787337 64612747401952278194840503)
      ·
        refine ⟨96919121102928417292260755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64612747401952278194840503 96919121102928417292260755)
        ·
          refine ⟨145378681654392625938391133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96919121102928417292260755 145378681654392625938391133)
          ·
            refine ⟨54517005620397234726896675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145378681654392625938391133 54517005620397234726896675)
            ·
              refine ⟨81775508430595852090345013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54517005620397234726896675 81775508430595852090345013)
              ·
                refine ⟨7666453915368361133469845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81775508430595852090345013 7666453915368361133469845)
                ·
                  refine ⟨359365027282891928131399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7666453915368361133469845 359365027282891928131399)
                  ·
                    rfl

theorem cell23_6298748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 1, 5, 6].length) (baseStart_6298748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298748 prefixEnd_6298748 := by exact prefixLift 6298748
  have htrace : WordTrace (prefixWord ++ tailWord_6298748) baseStart_6298748 baseEnd_6298748 := by
    simpa [prefixWord, tailWord_6298748, baseEnd_6298748] using wordTrace_append hprefix tailTrace_6298748
  have hstable : (prefixWord ++ tailWord_6298748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298748).length < 2 ^ (prefixWord ++ tailWord_6298748).sum := by decide
  have hdescent : baseEnd_6298748 < baseStart_6298748 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298782 : List Nat := [4, 3, 1, 1, 2, 1, 3, 2, 6]
def baseStart_6298782 : Nat := 118140960795 + 6298782 * 2 ^ 59
def prefixEnd_6298782 : Nat := 4983230072969 + 3 ^ 40 * 6298782 * 2
def baseEnd_6298782 : Nat := 359366967098697802239715

theorem tailTrace_6298782 : CollatzResearch.WordTrace tailWord_6298782 prefixEnd_6298782 359366967098697802239715 := by
  unfold tailWord_6298782
  simp only [CollatzResearch.WordTrace]
  refine ⟨28716931633324504395771325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153156968711064023444113733 28716931633324504395771325)
  ·
    refine ⟨10768849362496689148414247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28716931633324504395771325 10768849362496689148414247)
    ·
      refine ⟨16153274043745033722621371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10768849362496689148414247 16153274043745033722621371)
      ·
        refine ⟨24229911065617550583932057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16153274043745033722621371 24229911065617550583932057)
        ·
          refine ⟨18172433299213162937949043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24229911065617550583932057 18172433299213162937949043)
          ·
            refine ⟨27258649948819744406923565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18172433299213162937949043 27258649948819744406923565)
            ·
              refine ⟨10221993730807404152596337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27258649948819744406923565 10221993730807404152596337)
              ·
                refine ⟨7666495298105553114447253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10221993730807404152596337 7666495298105553114447253)
                ·
                  refine ⟨359366967098697802239715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7666495298105553114447253 359366967098697802239715)
                  ·
                    rfl

theorem cell23_6298782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 3, 2, 6].length) (baseStart_6298782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298782 prefixEnd_6298782 := by exact prefixLift 6298782
  have htrace : WordTrace (prefixWord ++ tailWord_6298782) baseStart_6298782 baseEnd_6298782 := by
    simpa [prefixWord, tailWord_6298782, baseEnd_6298782] using wordTrace_append hprefix tailTrace_6298782
  have hstable : (prefixWord ++ tailWord_6298782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298782).length < 2 ^ (prefixWord ++ tailWord_6298782).sum := by decide
  have hdescent : baseEnd_6298782 < baseStart_6298782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298808 : List Nat := [2, 1, 2, 1, 2, 1, 2, 5, 1, 6]
def baseStart_6298808 : Nat := 118140960795 + 6298808 * 2 ^ 59
def prefixEnd_6298808 : Nat := 4983230072969 + 3 ^ 40 * 6298808 * 2
def baseEnd_6298808 : Nat := 1078105351461765706144105

theorem tailTrace_6298808 : CollatzResearch.WordTrace tailWord_6298808 prefixEnd_6298808 1078105351461765706144105 := by
  unfold tailWord_6298808
  simp only [CollatzResearch.WordTrace]
  refine ⟨114868200682250920803308539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153157600909667894404411385 114868200682250920803308539)
  ·
    refine ⟨172302301023376381204962809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114868200682250920803308539 172302301023376381204962809)
    ·
      refine ⟨129226725767532285903722107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172302301023376381204962809 129226725767532285903722107)
      ·
        refine ⟨193840088651298428855583161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129226725767532285903722107 193840088651298428855583161)
        ·
          refine ⟨145380066488473821641687371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193840088651298428855583161 145380066488473821641687371)
          ·
            refine ⟨218070099732710732462531057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145380066488473821641687371 218070099732710732462531057)
            ·
              refine ⟨163552574799533049346898293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218070099732710732462531057 163552574799533049346898293)
              ·
                refine ⟨15333053887456223376271715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163552574799533049346898293 15333053887456223376271715)
                ·
                  refine ⟨22999580831184335064407573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15333053887456223376271715 22999580831184335064407573)
                  ·
                    refine ⟨1078105351461765706144105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22999580831184335064407573 1078105351461765706144105)
                    ·
                      rfl

theorem cell23_6298808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 2, 5, 1, 6].length) (baseStart_6298808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298808 prefixEnd_6298808 := by exact prefixLift 6298808
  have htrace : WordTrace (prefixWord ++ tailWord_6298808) baseStart_6298808 baseEnd_6298808 := by
    simpa [prefixWord, tailWord_6298808, baseEnd_6298808] using wordTrace_append hprefix tailTrace_6298808
  have hstable : (prefixWord ++ tailWord_6298808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298808).length < 2 ^ (prefixWord ++ tailWord_6298808).sum := by decide
  have hdescent : baseEnd_6298808 < baseStart_6298808 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298812 : List Nat := [2, 2, 2, 3, 2, 2, 2, 2, 1, 5]
def baseStart_6298812 : Nat := 118140960795 + 6298812 * 2 ^ 59
def prefixEnd_6298812 : Nat := 4983230072969 + 3 ^ 40 * 6298812 * 2
def baseEnd_6298812 : Nat := 1078106036102638367594099

theorem tailTrace_6298812 : CollatzResearch.WordTrace tailWord_6298812 prefixEnd_6298812 1078106036102638367594099 := by
  unfold tailWord_6298812
  simp only [CollatzResearch.WordTrace]
  refine ⟨114868273628243675144881345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153157698170991566859841793 114868273628243675144881345)
  ·
    refine ⟨86151205221182756358661009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114868273628243675144881345 86151205221182756358661009)
    ·
      refine ⟨64613403915887067268995757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86151205221182756358661009 64613403915887067268995757)
      ·
        refine ⟨24230026468457650225873409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64613403915887067268995757 24230026468457650225873409)
        ·
          refine ⟨18172519851343237669405057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24230026468457650225873409 18172519851343237669405057)
          ·
            refine ⟨13629389888507428252053793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18172519851343237669405057 13629389888507428252053793)
            ·
              refine ⟨10222042416380571189040345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13629389888507428252053793 10222042416380571189040345)
              ·
                refine ⟨7666531812285428391780259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10222042416380571189040345 7666531812285428391780259)
                ·
                  refine ⟨11499797718428142587670389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7666531812285428391780259 11499797718428142587670389)
                  ·
                    refine ⟨1078106036102638367594099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11499797718428142587670389 1078106036102638367594099)
                    ·
                      rfl

theorem cell23_6298812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 2, 2, 2, 1, 5].length) (baseStart_6298812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298812 prefixEnd_6298812 := by exact prefixLift 6298812
  have htrace : WordTrace (prefixWord ++ tailWord_6298812) baseStart_6298812 baseEnd_6298812 := by
    simpa [prefixWord, tailWord_6298812, baseEnd_6298812] using wordTrace_append hprefix tailTrace_6298812
  have hstable : (prefixWord ++ tailWord_6298812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298812).length < 2 ^ (prefixWord ++ tailWord_6298812).sum := by decide
  have hdescent : baseEnd_6298812 < baseStart_6298812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298815 : List Nat := [1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 4]
def baseStart_6298815 : Nat := 118140960795 + 6298815 * 2 ^ 59
def prefixEnd_6298815 : Nat := 4983230072969 + 3 ^ 40 * 6298815 * 2
def baseEnd_6298815 : Nat := 3234319648749878591044783

theorem tailTrace_6298815 : CollatzResearch.WordTrace tailWord_6298815 prefixEnd_6298815 3234319648749878591044783 := by
  unfold tailWord_6298815
  simp only [CollatzResearch.WordTrace]
  refine ⟨229736656675476481802121899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153157771116984321201414599 229736656675476481802121899)
  ·
    refine ⟨344604985013214722703182849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229736656675476481802121899 344604985013214722703182849)
    ·
      refine ⟨258453738759911042027387137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344604985013214722703182849 258453738759911042027387137)
      ·
        refine ⟨193840304069933281520540353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258453738759911042027387137 193840304069933281520540353)
        ·
          refine ⟨145380228052449961140405265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193840304069933281520540353 145380228052449961140405265)
          ·
            refine ⟨109035171039337470855303949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145380228052449961140405265 109035171039337470855303949)
            ·
              refine ⟨40888189139751551570738981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109035171039337470855303949 40888189139751551570738981)
              ·
                refine ⟨7666535463703415919513559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40888189139751551570738981 7666535463703415919513559)
                ·
                  refine ⟨11499803195555123879270339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7666535463703415919513559 11499803195555123879270339)
                  ·
                    refine ⟨17249704793332685818905509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11499803195555123879270339 17249704793332685818905509)
                    ·
                      refine ⟨3234319648749878591044783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17249704793332685818905509 3234319648749878591044783)
                      ·
                        rfl

theorem cell23_6298815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 4, 1, 1, 4].length) (baseStart_6298815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298815 prefixEnd_6298815 := by exact prefixLift 6298815
  have htrace : WordTrace (prefixWord ++ tailWord_6298815) baseStart_6298815 baseEnd_6298815 := by
    simpa [prefixWord, tailWord_6298815, baseEnd_6298815] using wordTrace_append hprefix tailTrace_6298815
  have hstable : (prefixWord ++ tailWord_6298815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298815).length < 2 ^ (prefixWord ++ tailWord_6298815).sum := by decide
  have hdescent : baseEnd_6298815 < baseStart_6298815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298826 : List Nat := [3, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3]
def baseStart_6298826 : Nat := 118140960795 + 6298826 * 2 ^ 59
def prefixEnd_6298826 : Nat := 4983230072969 + 3 ^ 40 * 6298826 * 2
def baseEnd_6298826 : Nat := 3234325297037078048007233

theorem tailTrace_6298826 : CollatzResearch.WordTrace tailWord_6298826 prefixEnd_6298826 3234325297037078048007233 := by
  unfold tailWord_6298826
  simp only [CollatzResearch.WordTrace]
  refine ⟨57434264469609157670193083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153158038585624420453848221 57434264469609157670193083)
  ·
    refine ⟨86151396704413736505289625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57434264469609157670193083 86151396704413736505289625)
    ·
      refine ⟨64613547528310302378967219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86151396704413736505289625 64613547528310302378967219)
      ·
        refine ⟨96920321292465453568450829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64613547528310302378967219 96920321292465453568450829)
        ·
          refine ⟨36345120484674545088169061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96920321292465453568450829 36345120484674545088169061)
          ·
            refine ⟨6814710090876477204031699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36345120484674545088169061 6814710090876477204031699)
            ·
              refine ⟨10222065136314715806047549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814710090876477204031699 10222065136314715806047549)
              ·
                refine ⟨3833274426118018427267831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10222065136314715806047549 3833274426118018427267831)
                ·
                  refine ⟨5749911639177027640901747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833274426118018427267831 5749911639177027640901747)
                  ·
                    refine ⟨8624867458765541461352621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5749911639177027640901747 8624867458765541461352621)
                    ·
                      refine ⟨3234325297037078048007233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8624867458765541461352621 3234325297037078048007233)
                      ·
                        rfl

theorem cell23_6298826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 3, 1, 1, 3].length) (baseStart_6298826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298826 prefixEnd_6298826 := by exact prefixLift 6298826
  have htrace : WordTrace (prefixWord ++ tailWord_6298826) baseStart_6298826 baseEnd_6298826 := by
    simpa [prefixWord, tailWord_6298826, baseEnd_6298826] using wordTrace_append hprefix tailTrace_6298826
  have hstable : (prefixWord ++ tailWord_6298826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298826).length < 2 ^ (prefixWord ++ tailWord_6298826).sum := by decide
  have hdescent : baseEnd_6298826 < baseStart_6298826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298836 : List Nat := [2, 4, 1, 4, 1, 1, 1, 2, 2, 3, 2]
def baseStart_6298836 : Nat := 118140960795 + 6298836 * 2 ^ 59
def prefixEnd_6298836 : Nat := 4983230072969 + 3 ^ 40 * 6298836 * 2
def baseEnd_6298836 : Nat := 3234330431843623008882187

theorem tailTrace_6298836 : CollatzResearch.WordTrace tailWord_6298836 prefixEnd_6298836 3234330431843623008882187 := by
  unfold tailWord_6298836
  simp only [CollatzResearch.WordTrace]
  refine ⟨114868711304200201194318181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153158281738933601592424241 114868711304200201194318181)
  ·
    refine ⟨21537883369537537723934659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114868711304200201194318181 21537883369537537723934659)
    ·
      refine ⟨32306825054306306585901989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21537883369537537723934659 32306825054306306585901989)
      ·
        refine ⟨6057529697682432484856623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32306825054306306585901989 6057529697682432484856623)
        ·
          refine ⟨9086294546523648727284935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6057529697682432484856623 9086294546523648727284935)
          ·
            refine ⟨13629441819785473090927403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9086294546523648727284935 13629441819785473090927403)
            ·
              refine ⟨20444162729678209636391105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13629441819785473090927403 20444162729678209636391105)
              ·
                refine ⟨15333122047258657227293329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20444162729678209636391105 15333122047258657227293329)
                ·
                  refine ⟨11499841535443992920469997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15333122047258657227293329 11499841535443992920469997)
                  ·
                    refine ⟨4312440575791497345176249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11499841535443992920469997 4312440575791497345176249)
                    ·
                      refine ⟨3234330431843623008882187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312440575791497345176249 3234330431843623008882187)
                      ·
                        rfl

theorem cell23_6298836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_6298836 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298836 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298836 prefixEnd_6298836 := by exact prefixLift 6298836
  have htrace : WordTrace (prefixWord ++ tailWord_6298836) baseStart_6298836 baseEnd_6298836 := by
    simpa [prefixWord, tailWord_6298836, baseEnd_6298836] using wordTrace_append hprefix tailTrace_6298836
  have hstable : (prefixWord ++ tailWord_6298836).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298836).length < 2 ^ (prefixWord ++ tailWord_6298836).sum := by decide
  have hdescent : baseEnd_6298836 < baseStart_6298836 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298849 : List Nat := [1, 2, 3, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_6298849 : Nat := 118140960795 + 6298849 * 2 ^ 59
def prefixEnd_6298849 : Nat := 4983230072969 + 3 ^ 40 * 6298849 * 2
def baseEnd_6298849 : Nat := 3234337107092131458019627

theorem tailTrace_6298849 : CollatzResearch.WordTrace tailWord_6298849 prefixEnd_6298849 3234337107092131458019627 := by
  unfold tailWord_6298849
  simp only [CollatzResearch.WordTrace]
  refine ⟨229737896757353305608859601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153158597838235537072573067 229737896757353305608859601)
  ·
    refine ⟨172303422568014979206644701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229737896757353305608859601 172303422568014979206644701)
    ·
      refine ⟨64613783463005617202491763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172303422568014979206644701 64613783463005617202491763)
      ·
        refine ⟨96920675194508425803737645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64613783463005617202491763 96920675194508425803737645)
        ·
          refine ⟨36345253197940659676401617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96920675194508425803737645 36345253197940659676401617)
          ·
            refine ⟨27258939898455494757301213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36345253197940659676401617 27258939898455494757301213)
            ·
              refine ⟨10222102461920810533987955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27258939898455494757301213 10222102461920810533987955)
              ·
                refine ⟨15333153692881215800981933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10222102461920810533987955 15333153692881215800981933)
                ·
                  refine ⟨5749932634830455925368225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15333153692881215800981933 5749932634830455925368225)
                  ·
                    refine ⟨4312449476122841944026169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5749932634830455925368225 4312449476122841944026169)
                    ·
                      refine ⟨3234337107092131458019627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312449476122841944026169 3234337107092131458019627)
                      ·
                        rfl

theorem cell23_6298849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_6298849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298849 prefixEnd_6298849 := by exact prefixLift 6298849
  have htrace : WordTrace (prefixWord ++ tailWord_6298849) baseStart_6298849 baseEnd_6298849 := by
    simpa [prefixWord, tailWord_6298849, baseEnd_6298849] using wordTrace_append hprefix tailTrace_6298849
  have hstable : (prefixWord ++ tailWord_6298849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298849).length < 2 ^ (prefixWord ++ tailWord_6298849).sum := by decide
  have hdescent : baseEnd_6298849 < baseStart_6298849 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298859 : List Nat := [1, 1, 1, 1, 2, 8, 2, 1, 2, 4]
def baseStart_6298859 : Nat := 118140960795 + 6298859 * 2 ^ 59
def prefixEnd_6298859 : Nat := 4983230072969 + 3 ^ 40 * 6298859 * 2
def baseEnd_6298859 : Nat := 1078114080632892139631527

theorem tailTrace_6298859 : CollatzResearch.WordTrace tailWord_6298859 prefixEnd_6298859 1078114080632892139631527 := by
  unfold tailWord_6298859
  simp only [CollatzResearch.WordTrace]
  refine ⟨229738261487317077316723631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153158840991544718211149087 229738261487317077316723631)
  ·
    refine ⟨344607392230975615975085447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229738261487317077316723631 344607392230975615975085447)
    ·
      refine ⟨516911088346463423962628171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344607392230975615975085447 516911088346463423962628171)
      ·
        refine ⟨775366632519695135943942257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516911088346463423962628171 775366632519695135943942257)
        ·
          refine ⟨581524974389771351957956693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775366632519695135943942257 581524974389771351957956693)
          ·
            refine ⟨6814745793630133030757305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 581524974389771351957956693 6814745793630133030757305)
            ·
              refine ⟨5111059345222599773067979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6814745793630133030757305 5111059345222599773067979)
              ·
                refine ⟨7666589017833899659601969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111059345222599773067979 7666589017833899659601969)
                ·
                  refine ⟨5749941763375424744701477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7666589017833899659601969 5749941763375424744701477)
                  ·
                    refine ⟨1078114080632892139631527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5749941763375424744701477 1078114080632892139631527)
                    ·
                      rfl

theorem cell23_6298859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 8, 2, 1, 2, 4].length) (baseStart_6298859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298859 prefixEnd_6298859 := by exact prefixLift 6298859
  have htrace : WordTrace (prefixWord ++ tailWord_6298859) baseStart_6298859 baseEnd_6298859 := by
    simpa [prefixWord, tailWord_6298859, baseEnd_6298859] using wordTrace_append hprefix tailTrace_6298859
  have hstable : (prefixWord ++ tailWord_6298859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298859).length < 2 ^ (prefixWord ++ tailWord_6298859).sum := by decide
  have hdescent : baseEnd_6298859 < baseStart_6298859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298865 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_6298865 : Nat := 118140960795 + 6298865 * 2 ^ 59
def prefixEnd_6298865 : Nat := 4983230072969 + 3 ^ 40 * 6298865 * 2
def baseEnd_6298865 : Nat := 3234345322782603395419553

theorem tailTrace_6298865 : CollatzResearch.WordTrace tailWord_6298865 prefixEnd_6298865 3234345322782603395419553 := by
  unfold tailWord_6298865
  simp only [CollatzResearch.WordTrace]
  refine ⟨229738480325295340341442049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153158986883530226894294699 229738480325295340341442049)
  ·
    refine ⟨172303860243971505256081537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229738480325295340341442049 172303860243971505256081537)
    ·
      refine ⟨129227895182978628942061153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172303860243971505256081537 129227895182978628942061153)
      ·
        refine ⟨96920921387233971706545865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129227895182978628942061153 96920921387233971706545865)
        ·
          refine ⟨72690691040425478779909399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96920921387233971706545865 72690691040425478779909399)
          ·
            refine ⟨109036036560638218169864099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72690691040425478779909399 109036036560638218169864099)
            ·
              refine ⟨163554054840957327254796149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109036036560638218169864099 163554054840957327254796149)
              ·
                refine ⟨15333192641339749430137139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163554054840957327254796149 15333192641339749430137139)
                ·
                  refine ⟨22999788962009624145205709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15333192641339749430137139 22999788962009624145205709)
                  ·
                    refine ⟨8624920860753609054452141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 22999788962009624145205709 8624920860753609054452141)
                    ·
                      refine ⟨3234345322782603395419553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8624920860753609054452141 3234345322782603395419553)
                      ·
                        rfl

theorem cell23_6298865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_6298865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298865 prefixEnd_6298865 := by exact prefixLift 6298865
  have htrace : WordTrace (prefixWord ++ tailWord_6298865) baseStart_6298865 baseEnd_6298865 := by
    simpa [prefixWord, tailWord_6298865, baseEnd_6298865] using wordTrace_append hprefix tailTrace_6298865
  have hstable : (prefixWord ++ tailWord_6298865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298865).length < 2 ^ (prefixWord ++ tailWord_6298865).sum := by decide
  have hdescent : baseEnd_6298865 < baseStart_6298865 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298866 : List Nat := [3, 2, 1, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_6298866 : Nat := 118140960795 + 6298866 * 2 ^ 59
def prefixEnd_6298866 : Nat := 4983230072969 + 3 ^ 40 * 6298866 * 2
def baseEnd_6298866 : Nat := 3234345836263257891507049

theorem tailTrace_6298866 : CollatzResearch.WordTrace tailWord_6298866 prefixEnd_6298866 3234345836263257891507049 := by
  unfold tailWord_6298866
  simp only [CollatzResearch.WordTrace]
  refine ⟨57434629199572929378057113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153159011198861145008152301 57434629199572929378057113)
  ·
    refine ⟨43075971899679697033542835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57434629199572929378057113 43075971899679697033542835)
    ·
      refine ⟨64613957849519545550314253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43075971899679697033542835 64613957849519545550314253)
      ·
        refine ⟨24230234193569829581367845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64613957849519545550314253 24230234193569829581367845)
        ·
          refine ⟨4543168911294343046506471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24230234193569829581367845 4543168911294343046506471)
          ·
            refine ⟨6814753366941514569759707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543168911294343046506471 6814753366941514569759707)
            ·
              refine ⟨10222130050412271854639561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6814753366941514569759707 10222130050412271854639561)
              ·
                refine ⟨7666597537809203890979671, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10222130050412271854639561 7666597537809203890979671)
                ·
                  refine ⟨11499896306713805836469507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7666597537809203890979671 11499896306713805836469507)
                  ·
                    refine ⟨17249844460070708754704261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11499896306713805836469507 17249844460070708754704261)
                    ·
                      refine ⟨3234345836263257891507049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17249844460070708754704261 3234345836263257891507049)
                      ·
                        rfl

theorem cell23_6298866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_6298866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298866 prefixEnd_6298866 := by exact prefixLift 6298866
  have htrace : WordTrace (prefixWord ++ tailWord_6298866) baseStart_6298866 baseEnd_6298866 := by
    simpa [prefixWord, tailWord_6298866, baseEnd_6298866] using wordTrace_append hprefix tailTrace_6298866
  have hstable : (prefixWord ++ tailWord_6298866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298866).length < 2 ^ (prefixWord ++ tailWord_6298866).sum := by decide
  have hdescent : baseEnd_6298866 < baseStart_6298866 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298909 : List Nat := [1, 4, 2, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_6298909 : Nat := 118140960795 + 6298909 * 2 ^ 59
def prefixEnd_6298909 : Nat := 4983230072969 + 3 ^ 40 * 6298909 * 2
def baseEnd_6298909 : Nat := 3234367915931401223269351

theorem tailTrace_6298909 : CollatzResearch.WordTrace tailWord_6298909 prefixEnd_6298909 3234367915931401223269351 := by
  unfold tailWord_6298909
  simp only [CollatzResearch.WordTrace]
  refine ⟨229740085137135935856043781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153160056758090623904029187 229740085137135935856043781)
  ·
    refine ⟨43076265963212987973008209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229740085137135935856043781 43076265963212987973008209)
    ·
      refine ⟨32307199472409740979756157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43076265963212987973008209 32307199472409740979756157)
      ·
        refine ⟨12115199802153652867408559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32307199472409740979756157 12115199802153652867408559)
        ·
          refine ⟨18172799703230479301112839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12115199802153652867408559 18172799703230479301112839)
          ·
            refine ⟨27259199554845718951669259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18172799703230479301112839 27259199554845718951669259)
            ·
              refine ⟨40888799332268578427503889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27259199554845718951669259 40888799332268578427503889)
              ·
                refine ⟨30666599499201433820627917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40888799332268578427503889 30666599499201433820627917)
                ·
                  refine ⟨11499974812200537682735469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30666599499201433820627917 11499974812200537682735469)
                  ·
                    refine ⟨4312490554575201631025801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11499974812200537682735469 4312490554575201631025801)
                    ·
                      refine ⟨3234367915931401223269351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312490554575201631025801 3234367915931401223269351)
                      ·
                        rfl

theorem cell23_6298909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_6298909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298909 prefixEnd_6298909 := by exact prefixLift 6298909
  have htrace : WordTrace (prefixWord ++ tailWord_6298909) baseStart_6298909 baseEnd_6298909 := by
    simpa [prefixWord, tailWord_6298909, baseEnd_6298909] using wordTrace_append hprefix tailTrace_6298909
  have hstable : (prefixWord ++ tailWord_6298909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298909).length < 2 ^ (prefixWord ++ tailWord_6298909).sum := by decide
  have hdescent : baseEnd_6298909 < baseStart_6298909 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298915 : List Nat := [1, 1, 1, 4, 2, 4, 1, 1, 2, 6]
def baseStart_6298915 : Nat := 118140960795 + 6298915 * 2 ^ 59
def prefixEnd_6298915 : Nat := 4983230072969 + 3 ^ 40 * 6298915 * 2
def baseEnd_6298915 : Nat := 1078123665605109399931441

theorem tailTrace_6298915 : CollatzResearch.WordTrace tailWord_6298915 prefixEnd_6298915 1078123665605109399931441 := by
  unfold tailWord_6298915
  simp only [CollatzResearch.WordTrace]
  refine ⟨229740303975114198880762199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153160202650076132587174799 229740303975114198880762199)
  ·
    refine ⟨344610455962671298321143299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229740303975114198880762199 344610455962671298321143299)
    ·
      refine ⟨516915683944006947481714949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344610455962671298321143299 516915683944006947481714949)
      ·
        refine ⟨96921690739501302652821553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516915683944006947481714949 96921690739501302652821553)
        ·
          refine ⟨72691268054625976989616165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96921690739501302652821553 72691268054625976989616165)
          ·
            refine ⟨13629612760242370685553031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72691268054625976989616165 13629612760242370685553031)
            ·
              refine ⟨20444419140363556028329547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13629612760242370685553031 20444419140363556028329547)
              ·
                refine ⟨30666628710545334042494321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20444419140363556028329547 30666628710545334042494321)
                ·
                  refine ⟨22999971532909000531870741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30666628710545334042494321 22999971532909000531870741)
                  ·
                    refine ⟨1078123665605109399931441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 22999971532909000531870741 1078123665605109399931441)
                    ·
                      rfl

theorem cell23_6298915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 4, 1, 1, 2, 6].length) (baseStart_6298915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298915 prefixEnd_6298915 := by exact prefixLift 6298915
  have htrace : WordTrace (prefixWord ++ tailWord_6298915) baseStart_6298915 baseEnd_6298915 := by
    simpa [prefixWord, tailWord_6298915, baseEnd_6298915] using wordTrace_append hprefix tailTrace_6298915
  have hstable : (prefixWord ++ tailWord_6298915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298915).length < 2 ^ (prefixWord ++ tailWord_6298915).sum := by decide
  have hdescent : baseEnd_6298915 < baseStart_6298915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6298956 : List Nat := [2, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2]
def baseStart_6298956 : Nat := 118140960795 + 6298956 * 2 ^ 59
def prefixEnd_6298956 : Nat := 4983230072969 + 3 ^ 40 * 6298956 * 2
def baseEnd_6298956 : Nat := 3234392049522162539381635

theorem tailTrace_6298956 : CollatzResearch.WordTrace tailWord_6298956 prefixEnd_6298956 3234392049522162539381635 := by
  unfold tailWord_6298956
  simp only [CollatzResearch.WordTrace]
  refine ⟨114870899683982831441502361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153161199578643775255336481 114870899683982831441502361)
  ·
    refine ⟨86153174762987123581126771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114870899683982831441502361 86153174762987123581126771)
    ·
      refine ⟨129229762144480685371690157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86153174762987123581126771 129229762144480685371690157)
      ·
        refine ⟨48461160804180257014383809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129229762144480685371690157 48461160804180257014383809)
        ·
          refine ⟨36345870603135192760787857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48461160804180257014383809 36345870603135192760787857)
          ·
            refine ⟨27259402952351394570590893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36345870603135192760787857 27259402952351394570590893)
            ·
              refine ⟨10222276107131772963971585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27259402952351394570590893 10222276107131772963971585)
              ·
                refine ⟨7666707080348829722978689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10222276107131772963971585 7666707080348829722978689)
                ·
                  refine ⟨5750030310261622292234017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7666707080348829722978689 5750030310261622292234017)
                  ·
                    refine ⟨4312522732696216719175513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750030310261622292234017 4312522732696216719175513)
                    ·
                      refine ⟨3234392049522162539381635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312522732696216719175513 3234392049522162539381635)
                      ·
                        rfl

theorem cell23_6298956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_6298956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6298956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6298956 prefixEnd_6298956 := by exact prefixLift 6298956
  have htrace : WordTrace (prefixWord ++ tailWord_6298956) baseStart_6298956 baseEnd_6298956 := by
    simpa [prefixWord, tailWord_6298956, baseEnd_6298956] using wordTrace_append hprefix tailTrace_6298956
  have hstable : (prefixWord ++ tailWord_6298956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6298956).length < 2 ^ (prefixWord ++ tailWord_6298956).sum := by decide
  have hdescent : baseEnd_6298956 < baseStart_6298956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6298956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299009 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 2, 5]
def baseStart_6299009 : Nat := 118140960795 + 6299009 * 2 ^ 59
def prefixEnd_6299009 : Nat := 4983230072969 + 3 ^ 40 * 6299009 * 2
def baseEnd_6299009 : Nat := 1078139754665616944006297

theorem tailTrace_6299009 : CollatzResearch.WordTrace tailWord_6299009 prefixEnd_6299009 1078139754665616944006297 := by
  unfold tailWord_6299009
  simp only [CollatzResearch.WordTrace]
  refine ⟨229743732436773652934684081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153162488291182435289789387 229743732436773652934684081)
  ·
    refine ⟨172307799327580239701013061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229743732436773652934684081 172307799327580239701013061)
    ·
      refine ⟨32307712373921294943939949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172307799327580239701013061 32307712373921294943939949)
      ·
        refine ⟨12115392140220485603977481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32307712373921294943939949 12115392140220485603977481)
        ·
          refine ⟨9086544105165364202983111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12115392140220485603977481 9086544105165364202983111)
          ·
            refine ⟨13629816157748046304474667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9086544105165364202983111 13629816157748046304474667)
            ·
              refine ⟨20444724236622069456712001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13629816157748046304474667 20444724236622069456712001)
              ·
                refine ⟨15333543177466552092534001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20444724236622069456712001 15333543177466552092534001)
                ·
                  refine ⟨11500157383099914069400501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15333543177466552092534001 11500157383099914069400501)
                  ·
                    refine ⟨1078139754665616944006297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11500157383099914069400501 1078139754665616944006297)
                    ·
                      rfl

theorem cell23_6299009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_6299009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299009 prefixEnd_6299009 := by exact prefixLift 6299009
  have htrace : WordTrace (prefixWord ++ tailWord_6299009) baseStart_6299009 baseEnd_6299009 := by
    simpa [prefixWord, tailWord_6299009, baseEnd_6299009] using wordTrace_append hprefix tailTrace_6299009
  have hstable : (prefixWord ++ tailWord_6299009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299009).length < 2 ^ (prefixWord ++ tailWord_6299009).sum := by decide
  have hdescent : baseEnd_6299009 < baseStart_6299009 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299012 : List Nat := [2, 3, 2, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_6299012 : Nat := 118140960795 + 6299012 * 2 ^ 59
def prefixEnd_6299012 : Nat := 4983230072969 + 3 ^ 40 * 6299012 * 2
def baseEnd_6299012 : Nat := 3234420804438814320281377

theorem tailTrace_6299012 : CollatzResearch.WordTrace tailWord_6299012 prefixEnd_6299012 3234420804438814320281377 := by
  unfold tailWord_6299012
  simp only [CollatzResearch.WordTrace]
  refine ⟨114871920927881392223521645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153162561237175189631362193 114871920927881392223521645)
  ·
    refine ⟨43076970347955522083820617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114871920927881392223521645 43076970347955522083820617)
    ·
      refine ⟨32307727760966641562865463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43076970347955522083820617 32307727760966641562865463)
      ·
        refine ⟨48461591641449962344298195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32307727760966641562865463 48461591641449962344298195)
        ·
          refine ⟨72692387462174943516447293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48461591641449962344298195 72692387462174943516447293)
          ·
            refine ⟨27259645298315603818667735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72692387462174943516447293 27259645298315603818667735)
            ·
              refine ⟨40889467947473405728001603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27259645298315603818667735 40889467947473405728001603)
              ·
                refine ⟨61334201921210108592002405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40889467947473405728001603 61334201921210108592002405)
                ·
                  refine ⟨11500162860226895361000451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61334201921210108592002405 11500162860226895361000451)
                  ·
                    refine ⟨17250244290340343041500677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11500162860226895361000451 17250244290340343041500677)
                    ·
                      refine ⟨3234420804438814320281377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17250244290340343041500677 3234420804438814320281377)
                      ·
                        rfl

theorem cell23_6299012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_6299012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299012 prefixEnd_6299012 := by exact prefixLift 6299012
  have htrace : WordTrace (prefixWord ++ tailWord_6299012) baseStart_6299012 baseEnd_6299012 := by
    simpa [prefixWord, tailWord_6299012, baseEnd_6299012] using wordTrace_append hprefix tailTrace_6299012
  have hstable : (prefixWord ++ tailWord_6299012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299012).length < 2 ^ (prefixWord ++ tailWord_6299012).sum := by decide
  have hdescent : baseEnd_6299012 < baseStart_6299012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299079 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 3]
def baseStart_6299079 : Nat := 118140960795 + 6299079 * 2 ^ 59
def prefixEnd_6299079 : Nat := 4983230072969 + 3 ^ 40 * 6299079 * 2
def baseEnd_6299079 : Nat := 3234455207642665558143569

theorem tailTrace_6299079 : CollatzResearch.WordTrace tailWord_6299079 prefixEnd_6299079 3234455207642665558143569 := by
  unfold tailWord_6299079
  simp only [CollatzResearch.WordTrace]
  refine ⟨229746285546520054889732291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153164190364346703259821527 229746285546520054889732291)
  ·
    refine ⟨344619428319780082334598437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229746285546520054889732291 344619428319780082334598437)
    ·
      refine ⟨64616142809958765437737207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344619428319780082334598437 64616142809958765437737207)
      ·
        refine ⟨96924214214938148156605811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64616142809958765437737207 96924214214938148156605811)
        ·
          refine ⟨145386321322407222234908717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96924214214938148156605811 145386321322407222234908717)
          ·
            refine ⟨54519870495902708338090769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145386321322407222234908717 54519870495902708338090769)
            ·
              refine ⟨40889902871927031253568077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54519870495902708338090769 40889902871927031253568077)
              ·
                refine ⟨15333713576972636720088029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40889902871927031253568077 15333713576972636720088029)
                ·
                  refine ⟨5750142591364738770033011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15333713576972636720088029 5750142591364738770033011)
                  ·
                    refine ⟨8625213887047108155049517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750142591364738770033011 8625213887047108155049517)
                    ·
                      refine ⟨3234455207642665558143569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625213887047108155049517 3234455207642665558143569)
                      ·
                        rfl

theorem cell23_6299079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_6299079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299079 prefixEnd_6299079 := by exact prefixLift 6299079
  have htrace : WordTrace (prefixWord ++ tailWord_6299079) baseStart_6299079 baseEnd_6299079 := by
    simpa [prefixWord, tailWord_6299079, baseEnd_6299079] using wordTrace_append hprefix tailTrace_6299079
  have hstable : (prefixWord ++ tailWord_6299079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299079).length < 2 ^ (prefixWord ++ tailWord_6299079).sum := by decide
  have hdescent : baseEnd_6299079 < baseStart_6299079 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299082 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 3, 5]
def baseStart_6299082 : Nat := 118140960795 + 6299082 * 2 ^ 59
def prefixEnd_6299082 : Nat := 4983230072969 + 3 ^ 40 * 6299082 * 2
def baseEnd_6299082 : Nat := 1078152249361543015468685

theorem tailTrace_6299082 : CollatzResearch.WordTrace tailWord_6299082 prefixEnd_6299082 1078152249361543015468685 := by
  unfold tailWord_6299082
  simp only [CollatzResearch.WordTrace]
  refine ⟨57436598741377296600522875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153164263310339457601394333 57436598741377296600522875)
  ·
    refine ⟨86154898112065944900784313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57436598741377296600522875 86154898112065944900784313)
    ·
      refine ⟨64616173584049458675588235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86154898112065944900784313 64616173584049458675588235)
      ·
        refine ⟨96924260376074188013382353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64616173584049458675588235 96924260376074188013382353)
        ·
          refine ⟨72693195282055641010036765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96924260376074188013382353 72693195282055641010036765)
          ·
            refine ⟨27259948230770865378763787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72693195282055641010036765 27259948230770865378763787)
            ·
              refine ⟨40889922346156298068145681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27259948230770865378763787 40889922346156298068145681)
              ·
                refine ⟨30667441759617223551109261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40889922346156298068145681 30667441759617223551109261)
                ·
                  refine ⟨11500290659856458831665973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30667441759617223551109261 11500290659856458831665973)
                  ·
                    refine ⟨1078152249361543015468685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11500290659856458831665973 1078152249361543015468685)
                    ·
                      rfl

theorem cell23_6299082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 3, 5].length) (baseStart_6299082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299082 prefixEnd_6299082 := by exact prefixLift 6299082
  have htrace : WordTrace (prefixWord ++ tailWord_6299082) baseStart_6299082 baseEnd_6299082 := by
    simpa [prefixWord, tailWord_6299082, baseEnd_6299082] using wordTrace_append hprefix tailTrace_6299082
  have hstable : (prefixWord ++ tailWord_6299082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299082).length < 2 ^ (prefixWord ++ tailWord_6299082).sum := by decide
  have hdescent : baseEnd_6299082 < baseStart_6299082 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299112 : List Nat := [2, 1, 4, 1, 1, 2, 1, 4, 1, 6]
def baseStart_6299112 : Nat := 118140960795 + 6299112 * 2 ^ 59
def prefixEnd_6299112 : Nat := 4983230072969 + 3 ^ 40 * 6299112 * 2
def baseEnd_6299112 : Nat := 1078157384168087976343639

theorem tailTrace_6299112 : CollatzResearch.WordTrace tailWord_6299112 prefixEnd_6299112 1078157384168087976343639 := by
  unfold tailWord_6299112
  simp only [CollatzResearch.WordTrace]
  refine ⟨114873744577700250762841795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153164992770267001017122393 114873744577700250762841795)
  ·
    refine ⟨172310616866550376144262693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114873744577700250762841795 172310616866550376144262693)
    ·
      refine ⟨32308240662478195527049255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172310616866550376144262693 32308240662478195527049255)
      ·
        refine ⟨48462360993717293290573883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32308240662478195527049255 48462360993717293290573883)
        ·
          refine ⟨72693541490575939935860825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48462360993717293290573883 72693541490575939935860825)
          ·
            refine ⟨54520156117931954951895619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72693541490575939935860825 54520156117931954951895619)
            ·
              refine ⟨81780234176897932427843429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54520156117931954951895619 81780234176897932427843429)
              ·
                refine ⟨15333793908168362330220643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81780234176897932427843429 15333793908168362330220643)
                ·
                  refine ⟨23000690862252543495330965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15333793908168362330220643 23000690862252543495330965)
                  ·
                    refine ⟨1078157384168087976343639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23000690862252543495330965 1078157384168087976343639)
                    ·
                      rfl

theorem cell23_6299112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_6299112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299112 prefixEnd_6299112 := by exact prefixLift 6299112
  have htrace : WordTrace (prefixWord ++ tailWord_6299112) baseStart_6299112 baseEnd_6299112 := by
    simpa [prefixWord, tailWord_6299112, baseEnd_6299112] using wordTrace_append hprefix tailTrace_6299112
  have hstable : (prefixWord ++ tailWord_6299112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299112).length < 2 ^ (prefixWord ++ tailWord_6299112).sum := by decide
  have hdescent : baseEnd_6299112 < baseStart_6299112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299132 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 3, 2, 4]
def baseStart_6299132 : Nat := 118140960795 + 6299132 * 2 ^ 59
def prefixEnd_6299132 : Nat := 4983230072969 + 3 ^ 40 * 6299132 * 2
def baseEnd_6299132 : Nat := 3234482422117353850780825

theorem tailTrace_6299132 : CollatzResearch.WordTrace tailWord_6299132 prefixEnd_6299132 3234482422117353850780825 := by
  unfold tailWord_6299132
  simp only [CollatzResearch.WordTrace]
  refine ⟨114874109307664022470705825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153165479076885363294274433 114874109307664022470705825)
  ·
    refine ⟨86155581980748016853029369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114874109307664022470705825 86155581980748016853029369)
    ·
      refine ⟨64616686485561012639772027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86155581980748016853029369 64616686485561012639772027)
      ·
        refine ⟨96925029728341518959658041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64616686485561012639772027 96925029728341518959658041)
        ·
          refine ⟨72693772296256139219743531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96925029728341518959658041 72693772296256139219743531)
          ·
            refine ⟨109040658444384208829615297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72693772296256139219743531 109040658444384208829615297)
            ·
              refine ⟨81780493833288156622211473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109040658444384208829615297 81780493833288156622211473)
              ·
                refine ⟨61335370374966117466658605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81780493833288156622211473 61335370374966117466658605)
                ·
                  refine ⟨23000763890612294049996977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61335370374966117466658605 23000763890612294049996977)
                  ·
                    refine ⟨17250572917959220537497733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23000763890612294049996977 17250572917959220537497733)
                    ·
                      refine ⟨3234482422117353850780825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17250572917959220537497733 3234482422117353850780825)
                      ·
                        rfl

theorem cell23_6299132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 3, 2, 4].length) (baseStart_6299132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299132 prefixEnd_6299132 := by exact prefixLift 6299132
  have htrace : WordTrace (prefixWord ++ tailWord_6299132) baseStart_6299132 baseEnd_6299132 := by
    simpa [prefixWord, tailWord_6299132, baseEnd_6299132] using wordTrace_append hprefix tailTrace_6299132
  have hstable : (prefixWord ++ tailWord_6299132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299132).length < 2 ^ (prefixWord ++ tailWord_6299132).sum := by decide
  have hdescent : baseEnd_6299132 < baseStart_6299132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299170 : List Nat := [3, 3, 1, 1, 1, 1, 5, 3, 1, 2, 2]
def baseStart_6299170 : Nat := 118140960795 + 6299170 * 2 ^ 59
def prefixEnd_6299170 : Nat := 4983230072969 + 3 ^ 40 * 6299170 * 2
def baseEnd_6299170 : Nat := 3234501934382224702105651

theorem tailTrace_6299170 : CollatzResearch.WordTrace tailWord_6299170 prefixEnd_6299170 3234501934382224702105651 := by
  unfold tailWord_6299170
  simp only [CollatzResearch.WordTrace]
  refine ⟨57437401147297594357823741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153166403059460251620863309 57437401147297594357823741)
  ·
    refine ⟨21539025430236597884183903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57437401147297594357823741 21539025430236597884183903)
    ·
      refine ⟨32308538145354896826275855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539025430236597884183903 32308538145354896826275855)
      ·
        refine ⟨48462807218032345239413783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32308538145354896826275855 48462807218032345239413783)
        ·
          refine ⟨72694210827048517859120675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48462807218032345239413783 72694210827048517859120675)
          ·
            refine ⟨109041316240572776788681013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72694210827048517859120675 109041316240572776788681013)
            ·
              refine ⟨10222623397553697823938845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109041316240572776788681013 10222623397553697823938845)
              ·
                refine ⟨3833483774082636683977067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10222623397553697823938845 3833483774082636683977067)
                ·
                  refine ⟨5750225661123955025965601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833483774082636683977067 5750225661123955025965601)
                  ·
                    refine ⟨4312669245842966269474201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750225661123955025965601 4312669245842966269474201)
                    ·
                      refine ⟨3234501934382224702105651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312669245842966269474201 3234501934382224702105651)
                      ·
                        rfl

theorem cell23_6299170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 3, 1, 2, 2].length) (baseStart_6299170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299170 prefixEnd_6299170 := by exact prefixLift 6299170
  have htrace : WordTrace (prefixWord ++ tailWord_6299170) baseStart_6299170 baseEnd_6299170 := by
    simpa [prefixWord, tailWord_6299170, baseEnd_6299170] using wordTrace_append hprefix tailTrace_6299170
  have hstable : (prefixWord ++ tailWord_6299170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299170).length < 2 ^ (prefixWord ++ tailWord_6299170).sum := by decide
  have hdescent : baseEnd_6299170 < baseStart_6299170 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299176 : List Nat := [2, 1, 5, 2, 3, 1, 9]
def baseStart_6299176 : Nat := 118140960795 + 6299176 * 2 ^ 59
def prefixEnd_6299176 : Nat := 4983230072969 + 3 ^ 40 * 6299176 * 2
def baseEnd_6299176 : Nat := 39932160682298168871983

theorem tailTrace_6299176 : CollatzResearch.WordTrace tailWord_6299176 prefixEnd_6299176 39932160682298168871983 := by
  unfold tailWord_6299176
  simp only [CollatzResearch.WordTrace]
  refine ⟨114874911713584320228006691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153166548951445760304008921 114874911713584320228006691)
  ·
    refine ⟨172312367570376480342010037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114874911713584320228006691 172312367570376480342010037)
    ·
      refine ⟨16154284459722795032063441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172312367570376480342010037 16154284459722795032063441)
      ·
        refine ⟨12115713344792096274047581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16154284459722795032063441 12115713344792096274047581)
        ·
          refine ⟨4543392504297036102767843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12115713344792096274047581 4543392504297036102767843)
          ·
            refine ⟨6815088756445554154151765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543392504297036102767843 6815088756445554154151765)
            ·
              refine ⟨39932160682298168871983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6815088756445554154151765 39932160682298168871983)
              ·
                rfl

theorem cell23_6299176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 3, 1, 9].length) (baseStart_6299176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299176 prefixEnd_6299176 := by exact prefixLift 6299176
  have htrace : WordTrace (prefixWord ++ tailWord_6299176) baseStart_6299176 baseEnd_6299176 := by
    simpa [prefixWord, tailWord_6299176, baseEnd_6299176] using wordTrace_append hprefix tailTrace_6299176
  have hstable : (prefixWord ++ tailWord_6299176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299176).length < 2 ^ (prefixWord ++ tailWord_6299176).sum := by decide
  have hdescent : baseEnd_6299176 < baseStart_6299176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299179 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 7, 3, 2]
def baseStart_6299179 : Nat := 118140960795 + 6299179 * 2 ^ 59
def prefixEnd_6299179 : Nat := 4983230072969 + 3 ^ 40 * 6299179 * 2
def baseEnd_6299179 : Nat := 3234506555708115166893109

theorem tailTrace_6299179 : CollatzResearch.WordTrace tailWord_6299179 prefixEnd_6299179 3234506555708115166893109 := by
  unfold tailWord_6299179
  simp only [CollatzResearch.WordTrace]
  refine ⟨229749932846157771968372591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153166621897438514645581727 229749932846157771968372591)
  ·
    refine ⟨344624899269236657952558887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229749932846157771968372591 344624899269236657952558887)
    ·
      refine ⟨516937348903854986928838331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344624899269236657952558887 516937348903854986928838331)
      ·
        refine ⟨775406023355782480393257497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516937348903854986928838331 775406023355782480393257497)
        ·
          refine ⟨581554517516836860294943123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 775406023355782480393257497 581554517516836860294943123)
          ·
            refine ⟨872331776275255290442414685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581554517516836860294943123 872331776275255290442414685)
            ·
              refine ⟨327124416103220733915905507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872331776275255290442414685 327124416103220733915905507)
              ·
                refine ⟨490686624154831100873858261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327124416103220733915905507 490686624154831100873858261)
                ·
                  refine ⟨11500467753628853926731053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 490686624154831100873858261 11500467753628853926731053)
                  ·
                    refine ⟨4312675407610820222524145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11500467753628853926731053 4312675407610820222524145)
                    ·
                      refine ⟨3234506555708115166893109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312675407610820222524145 3234506555708115166893109)
                      ·
                        rfl

theorem cell23_6299179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 7, 3, 2].length) (baseStart_6299179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299179 prefixEnd_6299179 := by exact prefixLift 6299179
  have htrace : WordTrace (prefixWord ++ tailWord_6299179) baseStart_6299179 baseEnd_6299179 := by
    simpa [prefixWord, tailWord_6299179, baseEnd_6299179] using wordTrace_append hprefix tailTrace_6299179
  have hstable : (prefixWord ++ tailWord_6299179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299179).length < 2 ^ (prefixWord ++ tailWord_6299179).sum := by decide
  have hdescent : baseEnd_6299179 < baseStart_6299179 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299186 : List Nat := [3, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_6299186 : Nat := 118140960795 + 6299186 * 2 ^ 59
def prefixEnd_6299186 : Nat := 4983230072969 + 3 ^ 40 * 6299186 * 2
def baseEnd_6299186 : Nat := 3234510150072696639505577

theorem tailTrace_6299186 : CollatzResearch.WordTrace tailWord_6299186 prefixEnd_6299186 3234510150072696639505577 := by
  unfold tailWord_6299186
  simp only [CollatzResearch.WordTrace]
  refine ⟨57437547039283103040969353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153166792104754941442584941 57437547039283103040969353)
  ·
    refine ⟨43078160279462327280727015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57437547039283103040969353 43078160279462327280727015)
    ·
      refine ⟨64617240419193490921090523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43078160279462327280727015 64617240419193490921090523)
      ·
        refine ⟨96925860628790236381635785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64617240419193490921090523 96925860628790236381635785)
        ·
          refine ⟨72694395471592677286226839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96925860628790236381635785 72694395471592677286226839)
          ·
            refine ⟨109041593207389015929340259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72694395471592677286226839 109041593207389015929340259)
            ·
              refine ⟨163562389811083523894010389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109041593207389015929340259 163562389811083523894010389)
              ·
                refine ⟨7666987022394540182531737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163562389811083523894010389 7666987022394540182531737)
                ·
                  refine ⟨5750240266795905136898803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7666987022394540182531737 5750240266795905136898803)
                  ·
                    refine ⟨8625360400193857705348205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750240266795905136898803 8625360400193857705348205)
                    ·
                      refine ⟨3234510150072696639505577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625360400193857705348205 3234510150072696639505577)
                      ·
                        rfl

theorem cell23_6299186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_6299186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299186 prefixEnd_6299186 := by exact prefixLift 6299186
  have htrace : WordTrace (prefixWord ++ tailWord_6299186) baseStart_6299186 baseEnd_6299186 := by
    simpa [prefixWord, tailWord_6299186, baseEnd_6299186] using wordTrace_append hprefix tailTrace_6299186
  have hstable : (prefixWord ++ tailWord_6299186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299186).length < 2 ^ (prefixWord ++ tailWord_6299186).sum := by decide
  have hdescent : baseEnd_6299186 < baseStart_6299186 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299209 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 5, 4, 2]
def baseStart_6299209 : Nat := 118140960795 + 6299209 * 2 ^ 59
def prefixEnd_6299209 : Nat := 4983230072969 + 3 ^ 40 * 6299209 * 2
def baseEnd_6299209 : Nat := 3234521960127750049517971

theorem tailTrace_6299209 : CollatzResearch.WordTrace tailWord_6299209 prefixEnd_6299209 3234521960127750049517971 := by
  unfold tailWord_6299209
  simp only [CollatzResearch.WordTrace]
  refine ⟨229751027036049087091964681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153167351357366058061309787 229751027036049087091964681)
  ·
    refine ⟨172313270277036815318973511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229751027036049087091964681 172313270277036815318973511)
    ·
      refine ⟨258469905415555222978460267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172313270277036815318973511 258469905415555222978460267)
      ·
        refine ⟨387704858123332834467690401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258469905415555222978460267 387704858123332834467690401)
        ·
          refine ⟨290778643592499625850767801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387704858123332834467690401 290778643592499625850767801)
          ·
            refine ⟨218083982694374719388075851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290778643592499625850767801 218083982694374719388075851)
            ·
              refine ⟨327125974041562079082113777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218083982694374719388075851 327125974041562079082113777)
              ·
                refine ⟨245344480531171559311585333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327125974041562079082113777 245344480531171559311585333)
                ·
                  refine ⟨23001045049797333685461125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245344480531171559311585333 23001045049797333685461125)
                  ·
                    refine ⟨4312695946837000066023961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23001045049797333685461125 4312695946837000066023961)
                    ·
                      refine ⟨3234521960127750049517971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312695946837000066023961 3234521960127750049517971)
                      ·
                        rfl

theorem cell23_6299209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 5, 4, 2].length) (baseStart_6299209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299209 prefixEnd_6299209 := by exact prefixLift 6299209
  have htrace : WordTrace (prefixWord ++ tailWord_6299209) baseStart_6299209 baseEnd_6299209 := by
    simpa [prefixWord, tailWord_6299209, baseEnd_6299209] using wordTrace_append hprefix tailTrace_6299209
  have hstable : (prefixWord ++ tailWord_6299209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299209).length < 2 ^ (prefixWord ++ tailWord_6299209).sum := by decide
  have hdescent : baseEnd_6299209 < baseStart_6299209 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299226 : List Nat := [3, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2]
def baseStart_6299226 : Nat := 118140960795 + 6299226 * 2 ^ 59
def prefixEnd_6299226 : Nat := 4983230072969 + 3 ^ 40 * 6299226 * 2
def baseEnd_6299226 : Nat := 3234530689298876483005393

theorem tailTrace_6299226 : CollatzResearch.WordTrace tailWord_6299226 prefixEnd_6299226 3234530689298876483005393 := by
  unfold tailWord_6299226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57437911769246874748833383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153167764717991665996889021 57437911769246874748833383)
  ·
    refine ⟨86156867653870312123250075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57437911769246874748833383 86156867653870312123250075)
    ·
      refine ⟨129235301480805468184875113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86156867653870312123250075 129235301480805468184875113)
      ·
        refine ⟨96926476110604101138656335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129235301480805468184875113 96926476110604101138656335)
        ·
          refine ⟨145389714165906151707984503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96926476110604101138656335 145389714165906151707984503)
          ·
            refine ⟨218084571248859227561976755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145389714165906151707984503 218084571248859227561976755)
            ·
              refine ⟨327126856873288841342965133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218084571248859227561976755 327126856873288841342965133)
              ·
                refine ⟨122672571327483315503611925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327126856873288841342965133 122672571327483315503611925)
                ·
                  refine ⟨5750276780975780414231809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 122672571327483315503611925 5750276780975780414231809)
                  ·
                    refine ⟨4312707585731835310673857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750276780975780414231809 4312707585731835310673857)
                    ·
                      refine ⟨3234530689298876483005393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312707585731835310673857 3234530689298876483005393)
                      ·
                        rfl

theorem cell23_6299226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 3, 6, 2, 2].length) (baseStart_6299226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299226 prefixEnd_6299226 := by exact prefixLift 6299226
  have htrace : WordTrace (prefixWord ++ tailWord_6299226) baseStart_6299226 baseEnd_6299226 := by
    simpa [prefixWord, tailWord_6299226, baseEnd_6299226] using wordTrace_append hprefix tailTrace_6299226
  have hstable : (prefixWord ++ tailWord_6299226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299226).length < 2 ^ (prefixWord ++ tailWord_6299226).sum := by decide
  have hdescent : baseEnd_6299226 < baseStart_6299226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299259 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3]
def baseStart_6299259 : Nat := 118140960795 + 6299259 * 2 ^ 59
def prefixEnd_6299259 : Nat := 4983230072969 + 3 ^ 40 * 6299259 * 2
def baseEnd_6299259 : Nat := 3234547634160474853892741

theorem tailTrace_6299259 : CollatzResearch.WordTrace tailWord_6299259 prefixEnd_6299259 3234547634160474853892741 := by
  unfold tailWord_6299259
  simp only [CollatzResearch.WordTrace]
  refine ⟨229752850685867945631284831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153168567123911963754189887 229752850685867945631284831)
  ·
    refine ⟨344629276028801918446927247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229752850685867945631284831 344629276028801918446927247)
    ·
      refine ⟨516943914043202877670390871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344629276028801918446927247 516943914043202877670390871)
      ·
        refine ⟨775415871064804316505586307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516943914043202877670390871 775415871064804316505586307)
        ·
          refine ⟨1163123806597206474758379461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775415871064804316505586307 1163123806597206474758379461)
          ·
            refine ⟨218085713736976214017196149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1163123806597206474758379461 218085713736976214017196149)
            ·
              refine ⟨20445535662841520064112139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218085713736976214017196149 20445535662841520064112139)
              ·
                refine ⟨30668303494262280096168209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20445535662841520064112139 30668303494262280096168209)
                ·
                  refine ⟨23001227620696710072126157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30668303494262280096168209 23001227620696710072126157)
                  ·
                    refine ⟨8625460357761266277047309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23001227620696710072126157 8625460357761266277047309)
                    ·
                      refine ⟨3234547634160474853892741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625460357761266277047309 3234547634160474853892741)
                      ·
                        rfl

theorem cell23_6299259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 2, 3, 3].length) (baseStart_6299259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299259 prefixEnd_6299259 := by exact prefixLift 6299259
  have htrace : WordTrace (prefixWord ++ tailWord_6299259) baseStart_6299259 baseEnd_6299259 := by
    simpa [prefixWord, tailWord_6299259, baseEnd_6299259] using wordTrace_append hprefix tailTrace_6299259
  have hstable : (prefixWord ++ tailWord_6299259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299259).length < 2 ^ (prefixWord ++ tailWord_6299259).sum := by decide
  have hdescent : baseEnd_6299259 < baseStart_6299259 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299299 : List Nat := [1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4]
def baseStart_6299299 : Nat := 118140960795 + 6299299 * 2 ^ 59
def prefixEnd_6299299 : Nat := 4983230072969 + 3 ^ 40 * 6299299 * 2
def baseEnd_6299299 : Nat := 3234568173386654697392557

theorem tailTrace_6299299 : CollatzResearch.WordTrace tailWord_6299299 prefixEnd_6299299 3234568173386654697392557 := by
  unfold tailWord_6299299
  simp only [CollatzResearch.WordTrace]
  refine ⟨229754309605723032462740951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153169539737148688308493967 229754309605723032462740951)
  ·
    refine ⟨344631464408584548694111427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229754309605723032462740951 344631464408584548694111427)
    ·
      refine ⟨516947196612876823041167141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344631464408584548694111427 516947196612876823041167141)
      ·
        refine ⟨96927599364914404320218839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 516947196612876823041167141 96927599364914404320218839)
        ·
          refine ⟨145391399047371606480328259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96927599364914404320218839 145391399047371606480328259)
          ·
            refine ⟨218087098571057409720492389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145391399047371606480328259 218087098571057409720492389)
            ·
              refine ⟨40891330982073264322592323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218087098571057409720492389 40891330982073264322592323)
              ·
                refine ⟨61336996473109896483888485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40891330982073264322592323 61336996473109896483888485)
                ·
                  refine ⟨11500686838708105590729091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61336996473109896483888485 11500686838708105590729091)
                  ·
                    refine ⟨17251030258062158386093637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11500686838708105590729091 17251030258062158386093637)
                    ·
                      refine ⟨3234568173386654697392557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17251030258062158386093637 3234568173386654697392557)
                      ·
                        rfl

theorem cell23_6299299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_6299299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299299 prefixEnd_6299299 := by exact prefixLift 6299299
  have htrace : WordTrace (prefixWord ++ tailWord_6299299) baseStart_6299299 baseEnd_6299299 := by
    simpa [prefixWord, tailWord_6299299, baseEnd_6299299] using wordTrace_append hprefix tailTrace_6299299
  have hstable : (prefixWord ++ tailWord_6299299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299299).length < 2 ^ (prefixWord ++ tailWord_6299299).sum := by decide
  have hdescent : baseEnd_6299299 < baseStart_6299299 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299336 : List Nat := [2, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3]
def baseStart_6299336 : Nat := 118140960795 + 6299336 * 2 ^ 59
def prefixEnd_6299336 : Nat := 4983230072969 + 3 ^ 40 * 6299336 * 2
def baseEnd_6299336 : Nat := 3234587172170871052629887

theorem tailTrace_6299336 : CollatzResearch.WordTrace tailWord_6299336 prefixEnd_6299336 3234587172170871052629887 := by
  unfold tailWord_6299336
  simp only [CollatzResearch.WordTrace]
  refine ⟨114877829553294493890918931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153170439404392658521225241 114877829553294493890918931)
  ·
    refine ⟨172316744329941740836378397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114877829553294493890918931 172316744329941740836378397)
    ·
      refine ⟨64618779123728152813641899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172316744329941740836378397 64618779123728152813641899)
      ·
        refine ⟨96928168685592229220462849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64618779123728152813641899 96928168685592229220462849)
        ·
          refine ⟨72696126514194171915347137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96928168685592229220462849 72696126514194171915347137)
          ·
            refine ⟨54522094885645628936510353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72696126514194171915347137 54522094885645628936510353)
            ·
              refine ⟨40891571164234221702382765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54522094885645628936510353 40891571164234221702382765)
              ·
                refine ⟨15334339186587833138393537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40891571164234221702382765 15334339186587833138393537)
                ·
                  refine ⟨11500754389940874853795153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15334339186587833138393537 11500754389940874853795153)
                  ·
                    refine ⟨8625565792455656140346365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11500754389940874853795153 8625565792455656140346365)
                    ·
                      refine ⟨3234587172170871052629887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625565792455656140346365 3234587172170871052629887)
                      ·
                        rfl

theorem cell23_6299336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_6299336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299336 prefixEnd_6299336 := by exact prefixLift 6299336
  have htrace : WordTrace (prefixWord ++ tailWord_6299336) baseStart_6299336 baseEnd_6299336 := by
    simpa [prefixWord, tailWord_6299336, baseEnd_6299336] using wordTrace_append hprefix tailTrace_6299336
  have hstable : (prefixWord ++ tailWord_6299336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299336).length < 2 ^ (prefixWord ++ tailWord_6299336).sum := by decide
  have hdescent : baseEnd_6299336 < baseStart_6299336 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299369 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 3, 5]
def baseStart_6299369 : Nat := 118140960795 + 6299369 * 2 ^ 59
def prefixEnd_6299369 : Nat := 4983230072969 + 3 ^ 40 * 6299369 * 2
def baseEnd_6299369 : Nat := 1078201372344156474505745

theorem tailTrace_6299369 : CollatzResearch.WordTrace tailWord_6299369 prefixEnd_6299369 1078201372344156474505745 := by
  unfold tailWord_6299369
  simp only [CollatzResearch.WordTrace]
  refine ⟨229756862715469434417789161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153171241810312956278526107 229756862715469434417789161)
  ·
    refine ⟨172317647036602075813341871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229756862715469434417789161 172317647036602075813341871)
    ·
      refine ⟨258476470554903113720012807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172317647036602075813341871 258476470554903113720012807)
      ·
        refine ⟨387714705832354670580019211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258476470554903113720012807 387714705832354670580019211)
        ·
          refine ⟨581572058748532005870028817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387714705832354670580019211 581572058748532005870028817)
          ·
            refine ⟨436179044061399004402521613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581572058748532005870028817 436179044061399004402521613)
            ·
              refine ⟨163567141523024626650945605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436179044061399004402521613 163567141523024626650945605)
              ·
                refine ⟨30668839035567117497052301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163567141523024626650945605 30668839035567117497052301)
                ·
                  refine ⟨11500814638337669061394613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30668839035567117497052301 11500814638337669061394613)
                  ·
                    refine ⟨1078201372344156474505745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11500814638337669061394613 1078201372344156474505745)
                    ·
                      rfl

theorem cell23_6299369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 3, 5].length) (baseStart_6299369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299369 prefixEnd_6299369 := by exact prefixLift 6299369
  have htrace : WordTrace (prefixWord ++ tailWord_6299369) baseStart_6299369 baseEnd_6299369 := by
    simpa [prefixWord, tailWord_6299369, baseEnd_6299369] using wordTrace_append hprefix tailTrace_6299369
  have hstable : (prefixWord ++ tailWord_6299369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299369).length < 2 ^ (prefixWord ++ tailWord_6299369).sum := by decide
  have hdescent : baseEnd_6299369 < baseStart_6299369 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299373 : List Nat := [1, 5, 1, 2, 1, 2, 4, 1, 6]
def baseStart_6299373 : Nat := 118140960795 + 6299373 * 2 ^ 59
def prefixEnd_6299373 : Nat := 4983230072969 + 3 ^ 40 * 6299373 * 2
def baseEnd_6299373 : Nat := 359400685661676378651913

theorem tailTrace_6299373 : CollatzResearch.WordTrace tailWord_6299373 prefixEnd_6299373 359400685661676378651913 := by
  unfold tailWord_6299373
  simp only [CollatzResearch.WordTrace]
  refine ⟨229757008607454943100934773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153171339071636628733956515 229757008607454943100934773)
  ·
    refine ⟨21539719556948900915712635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229757008607454943100934773 21539719556948900915712635)
    ·
      refine ⟨32309579335423351373568953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539719556948900915712635 32309579335423351373568953)
      ·
        refine ⟨24232184501567513530176715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32309579335423351373568953 24232184501567513530176715)
        ·
          refine ⟨36348276752351270295265073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24232184501567513530176715 36348276752351270295265073)
          ·
            refine ⟨27261207564263452721448805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36348276752351270295265073 27261207564263452721448805)
            ·
              refine ⟨5111476418299397385271651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27261207564263452721448805 5111476418299397385271651)
              ·
                refine ⟨7667214627449096077907477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111476418299397385271651 7667214627449096077907477)
                ·
                  refine ⟨359400685661676378651913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7667214627449096077907477 359400685661676378651913)
                  ·
                    rfl

theorem cell23_6299373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 4, 1, 6].length) (baseStart_6299373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299373 prefixEnd_6299373 := by exact prefixLift 6299373
  have htrace : WordTrace (prefixWord ++ tailWord_6299373) baseStart_6299373 baseEnd_6299373 := by
    simpa [prefixWord, tailWord_6299373, baseEnd_6299373] using wordTrace_append hprefix tailTrace_6299373
  have hstable : (prefixWord ++ tailWord_6299373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299373).length < 2 ^ (prefixWord ++ tailWord_6299373).sum := by decide
  have hdescent : baseEnd_6299373 < baseStart_6299373 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299376 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2]
def baseStart_6299376 : Nat := 118140960795 + 6299376 * 2 ^ 59
def prefixEnd_6299376 : Nat := 4983230072969 + 3 ^ 40 * 6299376 * 2
def baseEnd_6299376 : Nat := 3234607711397050896129703

theorem tailTrace_6299376 : CollatzResearch.WordTrace tailWord_6299376 prefixEnd_6299376 3234607711397050896129703 := by
  unfold tailWord_6299376
  simp only [CollatzResearch.WordTrace]
  refine ⟨114878559013222037306646991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153171412017629383075529321 114878559013222037306646991)
  ·
    refine ⟨172317838519833055959970487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114878559013222037306646991 172317838519833055959970487)
    ·
      refine ⟨258476757779749583939955731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172317838519833055959970487 258476757779749583939955731)
      ·
        refine ⟨387715136669624375909933597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258476757779749583939955731 387715136669624375909933597)
        ·
          refine ⟨145393176251109140966225099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387715136669624375909933597 145393176251109140966225099)
          ·
            refine ⟨218089764376663711449337649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145393176251109140966225099 218089764376663711449337649)
            ·
              refine ⟨163567323282497783587003237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218089764376663711449337649 163567323282497783587003237)
              ·
                refine ⟨30668873115468334422563107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163567323282497783587003237 30668873115468334422563107)
                ·
                  refine ⟨46003309673202501633844661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30668873115468334422563107 46003309673202501633844661)
                  ·
                    refine ⟨4312810281862734528172937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46003309673202501633844661 4312810281862734528172937)
                    ·
                      refine ⟨3234607711397050896129703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312810281862734528172937 3234607711397050896129703)
                      ·
                        rfl

theorem cell23_6299376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 1, 5, 2].length) (baseStart_6299376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299376 prefixEnd_6299376 := by exact prefixLift 6299376
  have htrace : WordTrace (prefixWord ++ tailWord_6299376) baseStart_6299376 baseEnd_6299376 := by
    simpa [prefixWord, tailWord_6299376, baseEnd_6299376] using wordTrace_append hprefix tailTrace_6299376
  have hstable : (prefixWord ++ tailWord_6299376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299376).length < 2 ^ (prefixWord ++ tailWord_6299376).sum := by decide
  have hdescent : baseEnd_6299376 < baseStart_6299376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299393 : List Nat := [1, 2, 4, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_6299393 : Nat := 118140960795 + 6299393 * 2 ^ 59
def prefixEnd_6299393 : Nat := 4983230072969 + 3 ^ 40 * 6299393 * 2
def baseEnd_6299393 : Nat := 3234616440568177329617125

theorem tailTrace_6299393 : CollatzResearch.WordTrace tailWord_6299393 prefixEnd_6299393 3234616440568177329617125 := by
  unfold tailWord_6299393
  simp only [CollatzResearch.WordTrace]
  refine ⟨229757738067382486516662833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153171825378254991011108555 229757738067382486516662833)
  ·
    refine ⟨172318303550536864887497125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229757738067382486516662833 172318303550536864887497125)
    ·
      refine ⟨32309681915725662166405711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172318303550536864887497125 32309681915725662166405711)
      ·
        refine ⟨48464522873588493249608567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32309681915725662166405711 48464522873588493249608567)
        ·
          refine ⟨72696784310382739874412851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48464522873588493249608567 72696784310382739874412851)
          ·
            refine ⟨109045176465574109811619277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72696784310382739874412851 109045176465574109811619277)
            ·
              refine ⟨40891941174590291179357229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109045176465574109811619277 40891941174590291179357229)
              ·
                refine ⟨15334477940471359192258961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40891941174590291179357229 15334477940471359192258961)
                ·
                  refine ⟨11500858455353519394194221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15334477940471359192258961 11500858455353519394194221)
                  ·
                    refine ⟨4312821920757569772822833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11500858455353519394194221 4312821920757569772822833)
                    ·
                      refine ⟨3234616440568177329617125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312821920757569772822833 3234616440568177329617125)
                      ·
                        rfl

theorem cell23_6299393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_6299393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299393 prefixEnd_6299393 := by exact prefixLift 6299393
  have htrace : WordTrace (prefixWord ++ tailWord_6299393) baseStart_6299393 baseEnd_6299393 := by
    simpa [prefixWord, tailWord_6299393, baseEnd_6299393] using wordTrace_append hprefix tailTrace_6299393
  have hstable : (prefixWord ++ tailWord_6299393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299393).length < 2 ^ (prefixWord ++ tailWord_6299393).sum := by decide
  have hdescent : baseEnd_6299393 < baseStart_6299393 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299400 : List Nat := [2, 1, 3, 2, 2, 1, 2, 5, 1, 1, 3]
def baseStart_6299400 : Nat := 118140960795 + 6299400 * 2 ^ 59
def prefixEnd_6299400 : Nat := 4983230072969 + 3 ^ 40 * 6299400 * 2
def baseEnd_6299400 : Nat := 3234620034932758802229593

theorem tailTrace_6299400 : CollatzResearch.WordTrace tailWord_6299400 prefixEnd_6299400 3234620034932758802229593 := by
  unfold tailWord_6299400
  simp only [CollatzResearch.WordTrace]
  refine ⟨114878996689178563356083827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153171995585571417808111769 114878996689178563356083827)
  ·
    refine ⟨172318495033767845034125741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114878996689178563356083827 172318495033767845034125741)
    ·
      refine ⟨64619435637662941887797153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172318495033767845034125741 64619435637662941887797153)
      ·
        refine ⟨48464576728247206415847865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64619435637662941887797153 48464576728247206415847865)
        ·
          refine ⟨36348432546185404811885899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48464576728247206415847865 36348432546185404811885899)
          ·
            refine ⟨54522648819278107217828849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36348432546185404811885899 54522648819278107217828849)
            ·
              refine ⟨40891986614458580413371637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54522648819278107217828849 40891986614458580413371637)
              ·
                refine ⟨3833623745105491913753591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 40891986614458580413371637 3833623745105491913753591)
                ·
                  refine ⟨5750435617658237870630387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833623745105491913753591 5750435617658237870630387)
                  ·
                    refine ⟨8625653426487356805945581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750435617658237870630387 8625653426487356805945581)
                    ·
                      refine ⟨3234620034932758802229593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625653426487356805945581 3234620034932758802229593)
                      ·
                        rfl

theorem cell23_6299400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_6299400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299400 prefixEnd_6299400 := by exact prefixLift 6299400
  have htrace : WordTrace (prefixWord ++ tailWord_6299400) baseStart_6299400 baseEnd_6299400 := by
    simpa [prefixWord, tailWord_6299400, baseEnd_6299400] using wordTrace_append hprefix tailTrace_6299400
  have hstable : (prefixWord ++ tailWord_6299400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299400).length < 2 ^ (prefixWord ++ tailWord_6299400).sum := by decide
  have hdescent : baseEnd_6299400 < baseStart_6299400 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299416 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 4, 4]
def baseStart_6299416 : Nat := 118140960795 + 6299416 * 2 ^ 59
def prefixEnd_6299416 : Nat := 4983230072969 + 3 ^ 40 * 6299416 * 2
def baseEnd_6299416 : Nat := 1078209416874410246543173

theorem tailTrace_6299416 : CollatzResearch.WordTrace tailWord_6299416 prefixEnd_6299416 1078209416874410246543173 := by
  unfold tailWord_6299416
  simp only [CollatzResearch.WordTrace]
  refine ⟨114879288473149580722375051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153172384630866107629833401 114879288473149580722375051)
  ·
    refine ⟨172318932709724371083562577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114879288473149580722375051 172318932709724371083562577)
    ·
      refine ⟨129239199532293278312671933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172318932709724371083562577 129239199532293278312671933)
      ·
        refine ⟨48464699824609979367251975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129239199532293278312671933 48464699824609979367251975)
        ·
          refine ⟨72697049736914969050877963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48464699824609979367251975 72697049736914969050877963)
          ·
            refine ⟨109045574605372453576316945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72697049736914969050877963 109045574605372453576316945)
            ·
              refine ⟨81784180954029340182237709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109045574605372453576316945 81784180954029340182237709)
              ·
                refine ⟨30669067857761002568339141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81784180954029340182237709 30669067857761002568339141)
                ·
                  refine ⟨5750450223330187981563589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30669067857761002568339141 5750450223330187981563589)
                  ·
                    refine ⟨1078209416874410246543173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5750450223330187981563589 1078209416874410246543173)
                    ·
                      rfl

theorem cell23_6299416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 4, 4].length) (baseStart_6299416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299416 prefixEnd_6299416 := by exact prefixLift 6299416
  have htrace : WordTrace (prefixWord ++ tailWord_6299416) baseStart_6299416 baseEnd_6299416 := by
    simpa [prefixWord, tailWord_6299416, baseEnd_6299416] using wordTrace_append hprefix tailTrace_6299416
  have hstable : (prefixWord ++ tailWord_6299416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299416).length < 2 ^ (prefixWord ++ tailWord_6299416).sum := by decide
  have hdescent : baseEnd_6299416 < baseStart_6299416 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299426 : List Nat := [3, 3, 1, 1, 2, 1, 2, 1, 3, 1, 5]
def baseStart_6299426 : Nat := 118140960795 + 6299426 * 2 ^ 59
def prefixEnd_6299426 : Nat := 4983230072969 + 3 ^ 40 * 6299426 * 2
def baseEnd_6299426 : Nat := 3234633385429775700504473

theorem tailTrace_6299426 : CollatzResearch.WordTrace tailWord_6299426 prefixEnd_6299426 3234633385429775700504473 := by
  unfold tailWord_6299426
  simp only [CollatzResearch.WordTrace]
  refine ⟨57439735419065733288153533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153172627784175288768409421 57439735419065733288153533)
  ·
    refine ⟨21539900782149649983057575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57439735419065733288153533 21539900782149649983057575)
    ·
      refine ⟨32309851173224474974586363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21539900782149649983057575 32309851173224474974586363)
      ·
        refine ⟨48464776759836712461879545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32309851173224474974586363 48464776759836712461879545)
        ·
          refine ⟨36348582569877534346409659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48464776759836712461879545 36348582569877534346409659)
          ·
            refine ⟨54522873854816301519614489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36348582569877534346409659 54522873854816301519614489)
            ·
              refine ⟨40892155391112226139710867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54522873854816301519614489 40892155391112226139710867)
              ·
                refine ⟨61338233086668339209566301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40892155391112226139710867 61338233086668339209566301)
                ·
                  refine ⟨23001837407500627203587363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61338233086668339209566301 23001837407500627203587363)
                  ·
                    refine ⟨34502756111250940805381045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23001837407500627203587363 34502756111250940805381045)
                    ·
                      refine ⟨3234633385429775700504473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34502756111250940805381045 3234633385429775700504473)
                      ·
                        rfl

theorem cell23_6299426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_6299426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299426 prefixEnd_6299426 := by exact prefixLift 6299426
  have htrace : WordTrace (prefixWord ++ tailWord_6299426) baseStart_6299426 baseEnd_6299426 := by
    simpa [prefixWord, tailWord_6299426, baseEnd_6299426] using wordTrace_append hprefix tailTrace_6299426
  have hstable : (prefixWord ++ tailWord_6299426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299426).length < 2 ^ (prefixWord ++ tailWord_6299426).sum := by decide
  have hdescent : baseEnd_6299426 < baseStart_6299426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299436 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 4]
def baseStart_6299436 : Nat := 118140960795 + 6299436 * 2 ^ 59
def prefixEnd_6299436 : Nat := 4983230072969 + 3 ^ 40 * 6299436 * 2
def baseEnd_6299436 : Nat := 3234638520236320661379427

theorem tailTrace_6299436 : CollatzResearch.WordTrace tailWord_6299436 prefixEnd_6299436 3234638520236320661379427 := by
  unfold tailWord_6299436
  simp only [CollatzResearch.WordTrace]
  refine ⟨114879653203113352430239081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153172870937484469906985441 114879653203113352430239081)
  ·
    refine ⟨86159739902335014322679311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114879653203113352430239081 86159739902335014322679311)
    ·
      refine ⟨129239609853502521484018967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86159739902335014322679311 129239609853502521484018967)
      ·
        refine ⟨193859414780253782226028451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129239609853502521484018967 193859414780253782226028451)
        ·
          refine ⟨290789122170380673339042677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193859414780253782226028451 290789122170380673339042677)
          ·
            refine ⟨27261480203473188125535251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290789122170380673339042677 27261480203473188125535251)
            ·
              refine ⟨40892220305209782188302877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27261480203473188125535251 40892220305209782188302877)
              ·
                refine ⟨15334582614453668320613579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40892220305209782188302877 15334582614453668320613579)
                ·
                  refine ⟨23001873921680502480920369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15334582614453668320613579 23001873921680502480920369)
                  ·
                    refine ⟨17251405441260376860690277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23001873921680502480920369 17251405441260376860690277)
                    ·
                      refine ⟨3234638520236320661379427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17251405441260376860690277 3234638520236320661379427)
                      ·
                        rfl

theorem cell23_6299436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 4].length) (baseStart_6299436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299436 prefixEnd_6299436 := by exact prefixLift 6299436
  have htrace : WordTrace (prefixWord ++ tailWord_6299436) baseStart_6299436 baseEnd_6299436 := by
    simpa [prefixWord, tailWord_6299436, baseEnd_6299436] using wordTrace_append hprefix tailTrace_6299436
  have hstable : (prefixWord ++ tailWord_6299436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299436).length < 2 ^ (prefixWord ++ tailWord_6299436).sum := by decide
  have hdescent : baseEnd_6299436 < baseStart_6299436 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299453 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_6299453 : Nat := 118140960795 + 6299453 * 2 ^ 59
def prefixEnd_6299453 : Nat := 4983230072969 + 3 ^ 40 * 6299453 * 2
def baseEnd_6299453 : Nat := 3234647249407447094866849

theorem tailTrace_6299453 : CollatzResearch.WordTrace tailWord_6299453 prefixEnd_6299453 3234647249407447094866849 := by
  unfold tailWord_6299453
  simp only [CollatzResearch.WordTrace]
  refine ⟨229759926447165116763847013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153173284298110077842564675 229759926447165116763847013)
  ·
    refine ⟨43079986208843459393221315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229759926447165116763847013 43079986208843459393221315)
    ·
      refine ⟨64619979313265189089831973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43079986208843459393221315 64619979313265189089831973)
      ·
        refine ⟨12116246121237222954343495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64619979313265189089831973 12116246121237222954343495)
        ·
          refine ⟨18174369181855834431515243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12116246121237222954343495 18174369181855834431515243)
          ·
            refine ⟨27261553772783751647272865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18174369181855834431515243 27261553772783751647272865)
            ·
              refine ⟨20446165329587813735454649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27261553772783751647272865 20446165329587813735454649)
              ·
                refine ⟨15334623997190860301590987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20446165329587813735454649 15334623997190860301590987)
                ·
                  refine ⟨23001935995786290452386481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15334623997190860301590987 23001935995786290452386481)
                  ·
                    refine ⟨17251451996839717839289861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23001935995786290452386481 17251451996839717839289861)
                    ·
                      refine ⟨3234647249407447094866849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17251451996839717839289861 3234647249407447094866849)
                      ·
                        rfl

theorem cell23_6299453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_6299453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299453 prefixEnd_6299453 := by exact prefixLift 6299453
  have htrace : WordTrace (prefixWord ++ tailWord_6299453) baseStart_6299453 baseEnd_6299453 := by
    simpa [prefixWord, tailWord_6299453, baseEnd_6299453] using wordTrace_append hprefix tailTrace_6299453
  have hstable : (prefixWord ++ tailWord_6299453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299453).length < 2 ^ (prefixWord ++ tailWord_6299453).sum := by decide
  have hdescent : baseEnd_6299453 < baseStart_6299453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299490 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 1, 3, 3]
def baseStart_6299490 : Nat := 118140960795 + 6299490 * 2 ^ 59
def prefixEnd_6299490 : Nat := 4983230072969 + 3 ^ 40 * 6299490 * 2
def baseEnd_6299490 : Nat := 3234666248191663450104179

theorem tailTrace_6299490 : CollatzResearch.WordTrace tailWord_6299490 prefixEnd_6299490 3234666248191663450104179 := by
  unfold tailWord_6299490
  simp only [CollatzResearch.WordTrace]
  refine ⟨57440318987007768020735981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153174183965354048055295949 57440318987007768020735981)
  ·
    refine ⟨21540119620127913007775993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57440318987007768020735981 21540119620127913007775993)
    ·
      refine ⟨16155089715095934755831995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21540119620127913007775993 16155089715095934755831995)
      ·
        refine ⟨24232634572643902133747993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16155089715095934755831995 24232634572643902133747993)
        ·
          refine ⟨18174475929482926600310995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24232634572643902133747993 18174475929482926600310995)
          ·
            refine ⟨27261713894224389900466493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18174475929482926600310995 27261713894224389900466493)
            ·
              refine ⟨10223142710334146212674935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27261713894224389900466493 10223142710334146212674935)
              ·
                refine ⟨15334714065501219319012403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10223142710334146212674935 15334714065501219319012403)
                ·
                  refine ⟨23002071098251828978518605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15334714065501219319012403 23002071098251828978518605)
                  ·
                    refine ⟨8625776661844435866944477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23002071098251828978518605 8625776661844435866944477)
                    ·
                      refine ⟨3234666248191663450104179, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625776661844435866944477 3234666248191663450104179)
                      ·
                        rfl

theorem cell23_6299490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_6299490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299490 prefixEnd_6299490 := by exact prefixLift 6299490
  have htrace : WordTrace (prefixWord ++ tailWord_6299490) baseStart_6299490 baseEnd_6299490 := by
    simpa [prefixWord, tailWord_6299490, baseEnd_6299490] using wordTrace_append hprefix tailTrace_6299490
  have hstable : (prefixWord ++ tailWord_6299490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299490).length < 2 ^ (prefixWord ++ tailWord_6299490).sum := by decide
  have hdescent : baseEnd_6299490 < baseStart_6299490 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299500 : List Nat := [2, 2, 1, 1, 4, 2, 1, 4, 1, 3, 2]
def baseStart_6299500 : Nat := 118140960795 + 6299500 * 2 ^ 59
def prefixEnd_6299500 : Nat := 4983230072969 + 3 ^ 40 * 6299500 * 2
def baseEnd_6299500 : Nat := 3234671382998208410979133

theorem tailTrace_6299500 : CollatzResearch.WordTrace tailWord_6299500 prefixEnd_6299500 3234671382998208410979133 := by
  unfold tailWord_6299500
  simp only [CollatzResearch.WordTrace]
  refine ⟨114880820338997421895403977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153174427118663229193871969 114880820338997421895403977)
  ·
    refine ⟨86160615254248066421552983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114880820338997421895403977 86160615254248066421552983)
    ·
      refine ⟨129240922881372099632329475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86160615254248066421552983 129240922881372099632329475)
      ·
        refine ⟨193861384322058149448494213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129240922881372099632329475 193861384322058149448494213)
        ·
          refine ⟨36349009560385903021592665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193861384322058149448494213 36349009560385903021592665)
          ·
            refine ⟨27261757170289427266194499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36349009560385903021592665 27261757170289427266194499)
            ·
              refine ⟨40892635755434140899291749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27261757170289427266194499 40892635755434140899291749)
              ·
                refine ⟨7667369204143901418617203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40892635755434140899291749 7667369204143901418617203)
                ·
                  refine ⟨11501053806215852127925805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7667369204143901418617203 11501053806215852127925805)
                  ·
                    refine ⟨4312895177330944547972177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11501053806215852127925805 4312895177330944547972177)
                    ·
                      refine ⟨3234671382998208410979133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312895177330944547972177 3234671382998208410979133)
                      ·
                        rfl

theorem cell23_6299500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 3, 2].length) (baseStart_6299500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299500 prefixEnd_6299500 := by exact prefixLift 6299500
  have htrace : WordTrace (prefixWord ++ tailWord_6299500) baseStart_6299500 baseEnd_6299500 := by
    simpa [prefixWord, tailWord_6299500, baseEnd_6299500] using wordTrace_append hprefix tailTrace_6299500
  have hstable : (prefixWord ++ tailWord_6299500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299500).length < 2 ^ (prefixWord ++ tailWord_6299500).sum := by decide
  have hdescent : baseEnd_6299500 < baseStart_6299500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299513 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 3, 4, 2]
def baseStart_6299513 : Nat := 118140960795 + 6299513 * 2 ^ 59
def prefixEnd_6299513 : Nat := 4983230072969 + 3 ^ 40 * 6299513 * 2
def baseEnd_6299513 : Nat := 3234678058246716860116573

theorem tailTrace_6299513 : CollatzResearch.WordTrace tailWord_6299513 prefixEnd_6299513 3234678058246716860116573 := by
  unfold tailWord_6299513
  simp only [CollatzResearch.WordTrace]
  refine ⟨229762114826947747011031193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153174743217965164674020795 229762114826947747011031193)
  ·
    refine ⟨172321586120210810258273395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229762114826947747011031193 172321586120210810258273395)
    ·
      refine ⟨258482379180316215387410093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172321586120210810258273395 258482379180316215387410093)
      ·
        refine ⟨96930892192618580770278785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258482379180316215387410093 96930892192618580770278785)
        ·
          refine ⟨72698169144463935577709089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96930892192618580770278785 72698169144463935577709089)
          ·
            refine ⟨54523626858347951683281817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72698169144463935577709089 54523626858347951683281817)
            ·
              refine ⟨40892720143760963762461363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54523626858347951683281817 40892720143760963762461363)
              ·
                refine ⟨61339080215641445643692045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40892720143760963762461363 61339080215641445643692045)
                ·
                  refine ⟨23002155080865542116384517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61339080215641445643692045 23002155080865542116384517)
                  ·
                    refine ⟨4312904077662289146822097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23002155080865542116384517 4312904077662289146822097)
                    ·
                      refine ⟨3234678058246716860116573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4312904077662289146822097 3234678058246716860116573)
                      ·
                        rfl

theorem cell23_6299513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 4, 2].length) (baseStart_6299513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299513 prefixEnd_6299513 := by exact prefixLift 6299513
  have htrace : WordTrace (prefixWord ++ tailWord_6299513) baseStart_6299513 baseEnd_6299513 := by
    simpa [prefixWord, tailWord_6299513, baseEnd_6299513] using wordTrace_append hprefix tailTrace_6299513
  have hstable : (prefixWord ++ tailWord_6299513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299513).length < 2 ^ (prefixWord ++ tailWord_6299513).sum := by decide
  have hdescent : baseEnd_6299513 < baseStart_6299513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299516 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 6, 3]
def baseStart_6299516 : Nat := 118140960795 + 6299516 * 2 ^ 59
def prefixEnd_6299516 : Nat := 4983230072969 + 3 ^ 40 * 6299516 * 2
def baseEnd_6299516 : Nat := 3234679598688680348379059

theorem tailTrace_6299516 : CollatzResearch.WordTrace tailWord_6299516 prefixEnd_6299516 3234679598688680348379059 := by
  unfold tailWord_6299516
  simp only [CollatzResearch.WordTrace]
  refine ⟨114881112122968439261695201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153174816163957919015593601 114881112122968439261695201)
  ·
    refine ⟨86160834092226329446271401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114881112122968439261695201 86160834092226329446271401)
    ·
      refine ⟨64620625569169747084703551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86160834092226329446271401 64620625569169747084703551)
      ·
        refine ⟨96930938353754620627055327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64620625569169747084703551 96930938353754620627055327)
        ·
          refine ⟨145396407530631930940582991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96930938353754620627055327 145396407530631930940582991)
          ·
            refine ⟨218094611295947896410874487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145396407530631930940582991 218094611295947896410874487)
            ·
              refine ⟨327141916943921844616311731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218094611295947896410874487 327141916943921844616311731)
              ·
                refine ⟨490712875415882766924467597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327141916943921844616311731 490712875415882766924467597)
                ·
                  refine ⟨184017328280956037596675349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 490712875415882766924467597 184017328280956037596675349)
                  ·
                    refine ⟨8625812263169814262344157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 184017328280956037596675349 8625812263169814262344157)
                    ·
                      refine ⟨3234679598688680348379059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8625812263169814262344157 3234679598688680348379059)
                      ·
                        rfl

theorem cell23_6299516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 6, 3].length) (baseStart_6299516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299516 prefixEnd_6299516 := by exact prefixLift 6299516
  have htrace : WordTrace (prefixWord ++ tailWord_6299516) baseStart_6299516 baseEnd_6299516 := by
    simpa [prefixWord, tailWord_6299516, baseEnd_6299516] using wordTrace_append hprefix tailTrace_6299516
  have hstable : (prefixWord ++ tailWord_6299516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299516).length < 2 ^ (prefixWord ++ tailWord_6299516).sum := by decide
  have hdescent : baseEnd_6299516 < baseStart_6299516 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299576 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5]
def baseStart_6299576 : Nat := 118140960795 + 6299576 * 2 ^ 59
def prefixEnd_6299576 : Nat := 4983230072969 + 3 ^ 40 * 6299576 * 2
def baseEnd_6299576 : Nat := 3234710407527950113628783

theorem tailTrace_6299576 : CollatzResearch.WordTrace tailWord_6299576 prefixEnd_6299576 3234710407527950113628783 := by
  unfold tailWord_6299576
  simp only [CollatzResearch.WordTrace]
  refine ⟨114882206312859754385287291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153176275083813005847049721 114882206312859754385287291)
  ·
    refine ⟨172323309469289631577930937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114882206312859754385287291 172323309469289631577930937)
    ·
      refine ⟨129242482101967223683448203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172323309469289631577930937 129242482101967223683448203)
      ·
        refine ⟨193863723152950835525172305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129242482101967223683448203 193863723152950835525172305)
        ·
          refine ⟨145397792364713126643879229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193863723152950835525172305 145397792364713126643879229)
          ·
            refine ⟨54524172136767422491454711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145397792364713126643879229 54524172136767422491454711)
            ·
              refine ⟨81786258205151133737182067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54524172136767422491454711 81786258205151133737182067)
              ·
                refine ⟨122679387307726700605773101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81786258205151133737182067 122679387307726700605773101)
                ·
                  refine ⟨46004770240397512727164913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122679387307726700605773101 46004770240397512727164913)
                  ·
                    refine ⟨34503577680298134545373685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46004770240397512727164913 34503577680298134545373685)
                    ·
                      refine ⟨3234710407527950113628783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34503577680298134545373685 3234710407527950113628783)
                      ·
                        rfl

theorem cell23_6299576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 2, 5].length) (baseStart_6299576 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299576 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299576 prefixEnd_6299576 := by exact prefixLift 6299576
  have htrace : WordTrace (prefixWord ++ tailWord_6299576) baseStart_6299576 baseEnd_6299576 := by
    simpa [prefixWord, tailWord_6299576, baseEnd_6299576] using wordTrace_append hprefix tailTrace_6299576
  have hstable : (prefixWord ++ tailWord_6299576).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299576).length < 2 ^ (prefixWord ++ tailWord_6299576).sum := by decide
  have hdescent : baseEnd_6299576 < baseStart_6299576 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299616 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6]
def baseStart_6299616 : Nat := 118140960795 + 6299616 * 2 ^ 59
def prefixEnd_6299616 : Nat := 4983230072969 + 3 ^ 40 * 6299616 * 2
def baseEnd_6299616 : Nat := 3234730946754129957128599

theorem tailTrace_6299616 : CollatzResearch.WordTrace tailWord_6299616 prefixEnd_6299616 3234730946754129957128599 := by
  unfold tailWord_6299616
  simp only [CollatzResearch.WordTrace]
  refine ⟨114882935772787297801015351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153177247697049730401353801 114882935772787297801015351)
  ·
    refine ⟨172324403659180946701523027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114882935772787297801015351 172324403659180946701523027)
    ·
      refine ⟨258486605488771420052284541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172324403659180946701523027 258486605488771420052284541)
      ·
        refine ⟨96932477058289282519606703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258486605488771420052284541 96932477058289282519606703)
        ·
          refine ⟨145398715587433923779410055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96932477058289282519606703 145398715587433923779410055)
          ·
            refine ⟨218098073381150885669115083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145398715587433923779410055 218098073381150885669115083)
            ·
              refine ⟨327147110071726328503672625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218098073381150885669115083 327147110071726328503672625)
              ·
                refine ⟨245360332553794746377754469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327147110071726328503672625 245360332553794746377754469)
                ·
                  refine ⟨46005062353836514945828963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 245360332553794746377754469 46005062353836514945828963)
                  ·
                    refine ⟨69007593530754772418743445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46005062353836514945828963 69007593530754772418743445)
                    ·
                      refine ⟨3234730946754129957128599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69007593530754772418743445 3234730946754129957128599)
                      ·
                        rfl

theorem cell23_6299616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_6299616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299616 prefixEnd_6299616 := by exact prefixLift 6299616
  have htrace : WordTrace (prefixWord ++ tailWord_6299616) baseStart_6299616 baseEnd_6299616 := by
    simpa [prefixWord, tailWord_6299616, baseEnd_6299616] using wordTrace_append hprefix tailTrace_6299616
  have hstable : (prefixWord ++ tailWord_6299616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299616).length < 2 ^ (prefixWord ++ tailWord_6299616).sum := by decide
  have hdescent : baseEnd_6299616 < baseStart_6299616 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299643 : List Nat := [1, 1, 1, 1, 1, 3, 7, 2, 6]
def baseStart_6299643 : Nat := 118140960795 + 6299643 * 2 ^ 59
def prefixEnd_6299643 : Nat := 4983230072969 + 3 ^ 40 * 6299643 * 2
def baseEnd_6299643 : Nat := 359416090081311261276775

theorem tailTrace_6299643 : CollatzResearch.WordTrace tailWord_6299643 prefixEnd_6299643 359416090081311261276775 := by
  unfold tailWord_6299643
  simp only [CollatzResearch.WordTrace]
  refine ⟨229766856316476779213263583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153177904210984519475509055 229766856316476779213263583)
  ·
    refine ⟨344650284474715168819895375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229766856316476779213263583 344650284474715168819895375)
    ·
      refine ⟨516975426712072753229843063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344650284474715168819895375 516975426712072753229843063)
      ·
        refine ⟨775463140068109129844764595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 516975426712072753229843063 775463140068109129844764595)
        ·
          refine ⟨1163194710102163694767146893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775463140068109129844764595 1163194710102163694767146893)
          ·
            refine ⟨436198016288311385537680085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163194710102163694767146893 436198016288311385537680085)
            ·
              refine ⟨10223391006757298098539377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 436198016288311385537680085 10223391006757298098539377)
              ·
                refine ⟨7667543255067973573904533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10223391006757298098539377 7667543255067973573904533)
                ·
                  refine ⟨359416090081311261276775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7667543255067973573904533 359416090081311261276775)
                  ·
                    rfl

theorem cell23_6299643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 7, 2, 6].length) (baseStart_6299643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299643 prefixEnd_6299643 := by exact prefixLift 6299643
  have htrace : WordTrace (prefixWord ++ tailWord_6299643) baseStart_6299643 baseEnd_6299643 := by
    simpa [prefixWord, tailWord_6299643, baseEnd_6299643] using wordTrace_append hprefix tailTrace_6299643
  have hstable : (prefixWord ++ tailWord_6299643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299643).length < 2 ^ (prefixWord ++ tailWord_6299643).sum := by decide
  have hdescent : baseEnd_6299643 < baseStart_6299643 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299660 : List Nat := [2, 2, 1, 2, 3, 1, 5, 1, 6]
def baseStart_6299660 : Nat := 118140960795 + 6299660 * 2 ^ 59
def prefixEnd_6299660 : Nat := 4983230072969 + 3 ^ 40 * 6299660 * 2
def baseEnd_6299660 : Nat := 359417059989214198330933

theorem tailTrace_6299660 : CollatzResearch.WordTrace tailWord_6299660 prefixEnd_6299660 359417059989214198330933 := by
  unfold tailWord_6299660
  simp only [CollatzResearch.WordTrace]
  refine ⟨114883738178707595558316217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153178317571610127411088289 114883738178707595558316217)
  ·
    refine ⟨86162803634030696668737163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114883738178707595558316217 86162803634030696668737163)
    ·
      refine ⟨129244205451046045003105745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86162803634030696668737163 129244205451046045003105745)
      ·
        refine ⟨96933154088284533752329309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129244205451046045003105745 96933154088284533752329309)
        ·
          refine ⟨36349932783106700157123491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96933154088284533752329309 36349932783106700157123491)
          ·
            refine ⟨54524899174660050235685237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36349932783106700157123491 54524899174660050235685237)
            ·
              refine ⟨5111709297624379709595491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54524899174660050235685237 5111709297624379709595491)
              ·
                refine ⟨7667563946436569564393237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111709297624379709595491 7667563946436569564393237)
                ·
                  refine ⟨359417059989214198330933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7667563946436569564393237 359417059989214198330933)
                  ·
                    rfl

theorem cell23_6299660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 5, 1, 6].length) (baseStart_6299660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299660 prefixEnd_6299660 := by exact prefixLift 6299660
  have htrace : WordTrace (prefixWord ++ tailWord_6299660) baseStart_6299660 baseEnd_6299660 := by
    simpa [prefixWord, tailWord_6299660, baseEnd_6299660] using wordTrace_append hprefix tailTrace_6299660
  have hstable : (prefixWord ++ tailWord_6299660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299660).length < 2 ^ (prefixWord ++ tailWord_6299660).sum := by decide
  have hdescent : baseEnd_6299660 < baseStart_6299660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299681 : List Nat := [1, 2, 3, 2, 5, 1, 1, 3, 1, 4]
def baseStart_6299681 : Nat := 118140960795 + 6299681 * 2 ^ 59
def prefixEnd_6299681 : Nat := 4983230072969 + 3 ^ 40 * 6299681 * 2
def baseEnd_6299681 : Nat := 1078254774332224067605267

theorem tailTrace_6299681 : CollatzResearch.WordTrace tailWord_6299681 prefixEnd_6299681 1078254774332224067605267 := by
  unfold tailWord_6299681
  simp only [CollatzResearch.WordTrace]
  refine ⟨229768242290339111703146897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153178828193559407802097931 229768242290339111703146897)
  ·
    refine ⟨172326181717754333777360173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229768242290339111703146897 172326181717754333777360173)
    ·
      refine ⟨64622318144157875166510065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172326181717754333777360173 64622318144157875166510065)
      ·
        refine ⟨48466738608118406374882549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64622318144157875166510065 48466738608118406374882549)
        ·
          refine ⟨4543756744511100597645239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48466738608118406374882549 4543756744511100597645239)
          ·
            refine ⟨6815635116766650896467859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4543756744511100597645239 6815635116766650896467859)
            ·
              refine ⟨10223452675149976344701789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6815635116766650896467859 10223452675149976344701789)
              ·
                refine ⟨3833794753181241129263171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10223452675149976344701789 3833794753181241129263171)
                ·
                  refine ⟨5750692129771861693894757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833794753181241129263171 5750692129771861693894757)
                  ·
                    refine ⟨1078254774332224067605267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5750692129771861693894757 1078254774332224067605267)
                    ·
                      rfl

theorem cell23_6299681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_6299681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299681 prefixEnd_6299681 := by exact prefixLift 6299681
  have htrace : WordTrace (prefixWord ++ tailWord_6299681) baseStart_6299681 baseEnd_6299681 := by
    simpa [prefixWord, tailWord_6299681, baseEnd_6299681] using wordTrace_append hprefix tailTrace_6299681
  have hstable : (prefixWord ++ tailWord_6299681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299681).length < 2 ^ (prefixWord ++ tailWord_6299681).sum := by decide
  have hdescent : baseEnd_6299681 < baseStart_6299681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299697 : List Nat := [1, 2, 2, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_6299697 : Nat := 118140960795 + 6299697 * 2 ^ 59
def prefixEnd_6299697 : Nat := 4983230072969 + 3 ^ 40 * 6299697 * 2
def baseEnd_6299697 : Nat := 3234772538687144140215727

theorem tailTrace_6299697 : CollatzResearch.WordTrace tailWord_6299697 prefixEnd_6299697 3234772538687144140215727 := by
  unfold tailWord_6299697
  simp only [CollatzResearch.WordTrace]
  refine ⟨229768825858281146435729345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153179217238854097623819563 229768825858281146435729345)
  ·
    refine ⟨172326619393710859826797009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229768825858281146435729345 172326619393710859826797009)
    ·
      refine ⟨129244964545283144870097757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172326619393710859826797009 129244964545283144870097757)
      ·
        refine ⟨48466861704481179326286659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129244964545283144870097757 48466861704481179326286659)
        ·
          refine ⟨72700292556721768989429989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48466861704481179326286659 72700292556721768989429989)
          ·
            refine ⟨13631304854385331685518123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72700292556721768989429989 13631304854385331685518123)
            ·
              refine ⟨20446957281577997528277185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13631304854385331685518123 20446957281577997528277185)
              ·
                refine ⟨15335217961183498146207889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20446957281577997528277185 15335217961183498146207889)
                ·
                  refine ⟨11501413470887623609655917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15335217961183498146207889 11501413470887623609655917)
                  ·
                    refine ⟨4313030051582858853620969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11501413470887623609655917 4313030051582858853620969)
                    ·
                      refine ⟨3234772538687144140215727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313030051582858853620969 3234772538687144140215727)
                      ·
                        rfl

theorem cell23_6299697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_6299697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299697 prefixEnd_6299697 := by exact prefixLift 6299697
  have htrace : WordTrace (prefixWord ++ tailWord_6299697) baseStart_6299697 baseEnd_6299697 := by
    simpa [prefixWord, tailWord_6299697, baseEnd_6299697] using wordTrace_append hprefix tailTrace_6299697
  have hstable : (prefixWord ++ tailWord_6299697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299697).length < 2 ^ (prefixWord ++ tailWord_6299697).sum := by decide
  have hdescent : baseEnd_6299697 < baseStart_6299697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299704 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3]
def baseStart_6299704 : Nat := 118140960795 + 6299704 * 2 ^ 59
def prefixEnd_6299704 : Nat := 4983230072969 + 3 ^ 40 * 6299704 * 2
def baseEnd_6299704 : Nat := 3234776133051725612828195

theorem tailTrace_6299704 : CollatzResearch.WordTrace tailWord_6299704 prefixEnd_6299704 3234776133051725612828195 := by
  unfold tailWord_6299704
  simp only [CollatzResearch.WordTrace]
  refine ⟨114884540584627893315617083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153179387446170524420822777 114884540584627893315617083)
  ·
    refine ⟨172326810876941839973425625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114884540584627893315617083 172326810876941839973425625)
    ·
      refine ⟨129245108157706379980069219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172326810876941839973425625 129245108157706379980069219)
      ·
        refine ⟨193867662236559569970103829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129245108157706379980069219 193867662236559569970103829)
        ·
          refine ⟨9087546667338729842348617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193867662236559569970103829 9087546667338729842348617)
          ·
            refine ⟨6815660000504047381761463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9087546667338729842348617 6815660000504047381761463)
            ·
              refine ⟨10223490000756071072642195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6815660000504047381761463 10223490000756071072642195)
              ·
                refine ⟨15335235001134106608963293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10223490000756071072642195 15335235001134106608963293)
                ·
                  refine ⟨5750713125425289978361235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15335235001134106608963293 5750713125425289978361235)
                  ·
                    refine ⟨8626069688137934967541853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750713125425289978361235 8626069688137934967541853)
                    ·
                      refine ⟨3234776133051725612828195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8626069688137934967541853 3234776133051725612828195)
                      ·
                        rfl

theorem cell23_6299704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 3, 1, 3].length) (baseStart_6299704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299704 prefixEnd_6299704 := by exact prefixLift 6299704
  have htrace : WordTrace (prefixWord ++ tailWord_6299704) baseStart_6299704 baseEnd_6299704 := by
    simpa [prefixWord, tailWord_6299704, baseEnd_6299704] using wordTrace_append hprefix tailTrace_6299704
  have hstable : (prefixWord ++ tailWord_6299704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299704).length < 2 ^ (prefixWord ++ tailWord_6299704).sum := by decide
  have hdescent : baseEnd_6299704 < baseStart_6299704 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299733 : List Nat := [1, 3, 2, 2, 1, 3, 2, 9]
def baseStart_6299733 : Nat := 118140960795 + 6299733 * 2 ^ 59
def prefixEnd_6299733 : Nat := 4983230072969 + 3 ^ 40 * 6299733 * 2
def baseEnd_6299733 : Nat := 119807074962618740717243

theorem tailTrace_6299733 : CollatzResearch.WordTrace tailWord_6299733 prefixEnd_6299733 119807074962618740717243 := by
  unfold tailWord_6299733
  simp only [CollatzResearch.WordTrace]
  refine ⟨229770138886150724584039853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153180092590767149722693235 229770138886150724584039853)
  ·
    refine ⟨86163802082306521719014945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229770138886150724584039853 86163802082306521719014945)
    ·
      refine ⟨64622851561729891289261209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86163802082306521719014945 64622851561729891289261209)
      ·
        refine ⟨48467138671297418466945907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64622851561729891289261209 48467138671297418466945907)
        ·
          refine ⟨72700708006946127700418861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48467138671297418466945907 72700708006946127700418861)
          ·
            refine ⟨27262765502604797887657073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72700708006946127700418861 27262765502604797887657073)
            ·
              refine ⟨20447074126953598415742805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27262765502604797887657073 20447074126953598415742805)
              ·
                refine ⟨119807074962618740717243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20447074126953598415742805 119807074962618740717243)
                ·
                  rfl

theorem cell23_6299733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 3, 2, 9].length) (baseStart_6299733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299733 prefixEnd_6299733 := by exact prefixLift 6299733
  have htrace : WordTrace (prefixWord ++ tailWord_6299733) baseStart_6299733 baseEnd_6299733 := by
    simpa [prefixWord, tailWord_6299733, baseEnd_6299733] using wordTrace_append hprefix tailTrace_6299733
  have hstable : (prefixWord ++ tailWord_6299733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299733).length < 2 ^ (prefixWord ++ tailWord_6299733).sum := by decide
  have hdescent : baseEnd_6299733 < baseStart_6299733 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299740 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 3, 2, 4]
def baseStart_6299740 : Nat := 118140960795 + 6299740 * 2 ^ 59
def prefixEnd_6299740 : Nat := 4983230072969 + 3 ^ 40 * 6299740 * 2
def baseEnd_6299740 : Nat := 3234794618355287471978029

theorem tailTrace_6299740 : CollatzResearch.WordTrace tailWord_6299740 prefixEnd_6299740 3234794618355287471978029 := by
  unfold tailWord_6299740
  simp only [CollatzResearch.WordTrace]
  refine ⟨114885197098562682389772337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153180262798083576519696449 114885197098562682389772337)
  ·
    refine ⟨86163897823922011792329253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114885197098562682389772337 86163897823922011792329253)
    ·
      refine ⟨16155730841985377211061735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86163897823922011792329253 16155730841985377211061735)
      ·
        refine ⟨24233596262978065816592603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16155730841985377211061735 24233596262978065816592603)
        ·
          refine ⟨36350394394467098724888905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24233596262978065816592603 36350394394467098724888905)
          ·
            refine ⟨27262795795850324043666679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36350394394467098724888905 27262795795850324043666679)
            ·
              refine ⟨40894193693775486065500019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27262795795850324043666679 40894193693775486065500019)
              ·
                refine ⟨61341290540663229098250029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40894193693775486065500019 61341290540663229098250029)
                ·
                  refine ⟨23002983952748710911843761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61341290540663229098250029 23002983952748710911843761)
                  ·
                    refine ⟨17252237964561533183882821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23002983952748710911843761 17252237964561533183882821)
                    ·
                      refine ⟨3234794618355287471978029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17252237964561533183882821 3234794618355287471978029)
                      ·
                        rfl

theorem cell23_6299740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_6299740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299740 prefixEnd_6299740 := by exact prefixLift 6299740
  have htrace : WordTrace (prefixWord ++ tailWord_6299740) baseStart_6299740 baseEnd_6299740 := by
    simpa [prefixWord, tailWord_6299740, baseEnd_6299740] using wordTrace_append hprefix tailTrace_6299740
  have hstable : (prefixWord ++ tailWord_6299740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299740).length < 2 ^ (prefixWord ++ tailWord_6299740).sum := by decide
  have hdescent : baseEnd_6299740 < baseStart_6299740 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299754 : List Nat := [3, 1, 3, 2, 3, 1, 2, 2, 2, 4]
def baseStart_6299754 : Nat := 118140960795 + 6299754 * 2 ^ 59
def prefixEnd_6299754 : Nat := 4983230072969 + 3 ^ 40 * 6299754 * 2
def baseEnd_6299754 : Nat := 1078267269028150139067655

theorem tailTrace_6299754 : CollatzResearch.WordTrace tailWord_6299754 prefixEnd_6299754 1078267269028150139067655 := by
  unfold tailWord_6299754
  simp only [CollatzResearch.WordTrace]
  refine ⟨57442726204768661292638579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153180603212716430113702877 57442726204768661292638579)
  ·
    refine ⟨86164089307152991938957869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57442726204768661292638579 86164089307152991938957869)
    ·
      refine ⟨32311533490182371977109201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86164089307152991938957869 32311533490182371977109201)
      ·
        refine ⟨24233650117636778982831901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32311533490182371977109201 24233650117636778982831901)
        ·
          refine ⟨9087618794113792118561963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24233650117636778982831901 9087618794113792118561963)
          ·
            refine ⟨13631428191170688177842945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9087618794113792118561963 13631428191170688177842945)
            ·
              refine ⟨10223571143378016133382209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13631428191170688177842945 10223571143378016133382209)
              ·
                refine ⟨7667678357533512100036657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10223571143378016133382209 7667678357533512100036657)
                ·
                  refine ⟨5750758768150134075027493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667678357533512100036657 5750758768150134075027493)
                  ·
                    refine ⟨1078267269028150139067655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5750758768150134075027493 1078267269028150139067655)
                    ·
                      rfl

theorem cell23_6299754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 1, 2, 2, 2, 4].length) (baseStart_6299754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299754 prefixEnd_6299754 := by exact prefixLift 6299754
  have htrace : WordTrace (prefixWord ++ tailWord_6299754) baseStart_6299754 baseEnd_6299754 := by
    simpa [prefixWord, tailWord_6299754, baseEnd_6299754] using wordTrace_append hprefix tailTrace_6299754
  have hstable : (prefixWord ++ tailWord_6299754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299754).length < 2 ^ (prefixWord ++ tailWord_6299754).sum := by decide
  have hdescent : baseEnd_6299754 < baseStart_6299754 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299804 : List Nat := [2, 2, 3, 2, 1, 1, 3, 3, 1, 3, 2]
def baseStart_6299804 : Nat := 118140960795 + 6299804 * 2 ^ 59
def prefixEnd_6299804 : Nat := 4983230072969 + 3 ^ 40 * 6299804 * 2
def baseEnd_6299804 : Nat := 3234827481117175221577735

theorem tailTrace_6299804 : CollatzResearch.WordTrace tailWord_6299804 prefixEnd_6299804 3234827481117175221577735 := by
  unfold tailWord_6299804
  simp only [CollatzResearch.WordTrace]
  refine ⟨114886364234446751854937233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153181818979262335806582977 114886364234446751854937233)
  ·
    refine ⟨86164773175835063891202925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114886364234446751854937233 86164773175835063891202925)
    ·
      refine ⟨32311789940938148959201097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86164773175835063891202925 32311789940938148959201097)
      ·
        refine ⟨24233842455703611719400823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32311789940938148959201097 24233842455703611719400823)
        ·
          refine ⟨36350763683555417579101235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24233842455703611719400823 36350763683555417579101235)
          ·
            refine ⟨54526145525333126368651853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36350763683555417579101235 54526145525333126368651853)
            ·
              refine ⟨20447304571999922388244445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54526145525333126368651853 20447304571999922388244445)
              ·
                refine ⟨7667739214499970895591667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20447304571999922388244445 7667739214499970895591667)
                ·
                  refine ⟨11501608821749956343387501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7667739214499970895591667 11501608821749956343387501)
                  ·
                    refine ⟨4313103308156233628770313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11501608821749956343387501 4313103308156233628770313)
                    ·
                      refine ⟨3234827481117175221577735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313103308156233628770313 3234827481117175221577735)
                      ·
                        rfl

theorem cell23_6299804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_6299804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299804 prefixEnd_6299804 := by exact prefixLift 6299804
  have htrace : WordTrace (prefixWord ++ tailWord_6299804) baseStart_6299804 baseEnd_6299804 := by
    simpa [prefixWord, tailWord_6299804, baseEnd_6299804] using wordTrace_append hprefix tailTrace_6299804
  have hstable : (prefixWord ++ tailWord_6299804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299804).length < 2 ^ (prefixWord ++ tailWord_6299804).sum := by decide
  have hdescent : baseEnd_6299804 < baseStart_6299804 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299834 : List Nat := [3, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2]
def baseStart_6299834 : Nat := 118140960795 + 6299834 * 2 ^ 59
def prefixEnd_6299834 : Nat := 4983230072969 + 3 ^ 40 * 6299834 * 2
def baseEnd_6299834 : Nat := 3234842885536810104202597

theorem tailTrace_6299834 : CollatzResearch.WordTrace tailWord_6299834 prefixEnd_6299834 3234842885536810104202597 := by
  unfold tailWord_6299834
  simp only [CollatzResearch.WordTrace]
  refine ⟨57443455664696204708366639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153182548439189879222311037 57443455664696204708366639)
  ·
    refine ⟨86165183497044307062549959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57443455664696204708366639 86165183497044307062549959)
    ·
      refine ⟨129247775245566460593824939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86165183497044307062549959 129247775245566460593824939)
      ·
        refine ⟨193871662868349690890737409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129247775245566460593824939 193871662868349690890737409)
        ·
          refine ⟨145403747151262268168053057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193871662868349690890737409 145403747151262268168053057)
          ·
            refine ⟨109052810363446701126039793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145403747151262268168053057 109052810363446701126039793)
            ·
              refine ⟨81789607772585025844529845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109052810363446701126039793 81789607772585025844529845)
              ·
                refine ⟨7667775728679846172924673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81789607772585025844529845 7667775728679846172924673)
                ·
                  refine ⟨5750831796509884629693505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667775728679846172924673 5750831796509884629693505)
                  ·
                    refine ⟨4313123847382413472270129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750831796509884629693505 4313123847382413472270129)
                    ·
                      refine ⟨3234842885536810104202597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313123847382413472270129 3234842885536810104202597)
                      ·
                        rfl

theorem cell23_6299834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 2, 5, 2, 2, 2].length) (baseStart_6299834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299834 prefixEnd_6299834 := by exact prefixLift 6299834
  have htrace : WordTrace (prefixWord ++ tailWord_6299834) baseStart_6299834 baseEnd_6299834 := by
    simpa [prefixWord, tailWord_6299834, baseEnd_6299834] using wordTrace_append hprefix tailTrace_6299834
  have hstable : (prefixWord ++ tailWord_6299834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299834).length < 2 ^ (prefixWord ++ tailWord_6299834).sum := by decide
  have hdescent : baseEnd_6299834 < baseStart_6299834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299840 : List Nat := [2, 1, 1, 2, 5, 1, 2, 2, 7]
def baseStart_6299840 : Nat := 118140960795 + 6299840 * 2 ^ 59
def prefixEnd_6299840 : Nat := 4983230072969 + 3 ^ 40 * 6299840 * 2
def baseEnd_6299840 : Nat := 359427329602304120080841

theorem tailTrace_6299840 : CollatzResearch.WordTrace tailWord_6299840 prefixEnd_6299840 359427329602304120080841 := by
  unfold tailWord_6299840
  simp only [CollatzResearch.WordTrace]
  refine ⟨114887020748381540929092487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153182694331175387905456649 114887020748381540929092487)
  ·
    refine ⟨172330531122572311393638731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114887020748381540929092487 172330531122572311393638731)
    ·
      refine ⟨258495796683858467090458097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172330531122572311393638731 258495796683858467090458097)
      ·
        refine ⟨193871847512893850317843573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258495796683858467090458097 193871847512893850317843573)
        ·
          refine ⟨18175485704333798467297835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193871847512893850317843573 18175485704333798467297835)
          ·
            refine ⟨27263228556500697700946753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18175485704333798467297835 27263228556500697700946753)
            ·
              refine ⟨20447421417375523275710065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27263228556500697700946753 20447421417375523275710065)
              ·
                refine ⟨15335566063031642456782549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20447421417375523275710065 15335566063031642456782549)
                ·
                  refine ⟨359427329602304120080841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15335566063031642456782549 359427329602304120080841)
                  ·
                    rfl

theorem cell23_6299840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 1, 2, 2, 7].length) (baseStart_6299840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299840 prefixEnd_6299840 := by exact prefixLift 6299840
  have htrace : WordTrace (prefixWord ++ tailWord_6299840) baseStart_6299840 baseEnd_6299840 := by
    simpa [prefixWord, tailWord_6299840, baseEnd_6299840] using wordTrace_append hprefix tailTrace_6299840
  have hstable : (prefixWord ++ tailWord_6299840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299840).length < 2 ^ (prefixWord ++ tailWord_6299840).sum := by decide
  have hdescent : baseEnd_6299840 < baseStart_6299840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299843 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6]
def baseStart_6299843 : Nat := 118140960795 + 6299843 * 2 ^ 59
def prefixEnd_6299843 : Nat := 4983230072969 + 3 ^ 40 * 6299843 * 2
def baseEnd_6299843 : Nat := 3234847506862700568990055

theorem tailTrace_6299843 : CollatzResearch.WordTrace tailWord_6299843 prefixEnd_6299843 3234847506862700568990055 := by
  unfold tailWord_6299843
  simp only [CollatzResearch.WordTrace]
  refine ⟨229774150915752213370544183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153182767277168142247029455 229774150915752213370544183)
  ·
    refine ⟨344661226373628320055816275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229774150915752213370544183 344661226373628320055816275)
    ·
      refine ⟨516991839560442480083724413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344661226373628320055816275 516991839560442480083724413)
      ·
        refine ⟨193871939835165930031396655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516991839560442480083724413 193871939835165930031396655)
        ·
          refine ⟨290807909752748895047094983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193871939835165930031396655 290807909752748895047094983)
          ·
            refine ⟨436211864629123342570642475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290807909752748895047094983 436211864629123342570642475)
            ·
              refine ⟨654317796943685013855963713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436211864629123342570642475 654317796943685013855963713)
              ·
                refine ⟨490738347707763760391972785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654317796943685013855963713 490738347707763760391972785)
                ·
                  refine ⟨368053760780822820293979589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490738347707763760391972785 368053760780822820293979589)
                  ·
                    refine ⟨69010080146404278805121173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 368053760780822820293979589 69010080146404278805121173)
                    ·
                      refine ⟨3234847506862700568990055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69010080146404278805121173 3234847506862700568990055)
                      ·
                        rfl

theorem cell23_6299843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_6299843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299843 prefixEnd_6299843 := by exact prefixLift 6299843
  have htrace : WordTrace (prefixWord ++ tailWord_6299843) baseStart_6299843 baseEnd_6299843 := by
    simpa [prefixWord, tailWord_6299843, baseEnd_6299843] using wordTrace_append hprefix tailTrace_6299843
  have hstable : (prefixWord ++ tailWord_6299843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299843).length < 2 ^ (prefixWord ++ tailWord_6299843).sum := by decide
  have hdescent : baseEnd_6299843 < baseStart_6299843 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299857 : List Nat := [1, 2, 2, 1, 2, 2, 5, 3, 5]
def baseStart_6299857 : Nat := 118140960795 + 6299857 * 2 ^ 59
def prefixEnd_6299857 : Nat := 4983230072969 + 3 ^ 40 * 6299857 * 2
def baseEnd_6299857 : Nat := 359428299510207057134999

theorem tailTrace_6299857 : CollatzResearch.WordTrace tailWord_6299857 prefixEnd_6299857 359428299510207057134999 := by
  unfold tailWord_6299857
  simp only [CollatzResearch.WordTrace]
  refine ⟨229774661537701493761553825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153183107691800995841035883 229774661537701493761553825)
  ·
    refine ⟨172330996153276120321165369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229774661537701493761553825 172330996153276120321165369)
    ·
      refine ⟨129248247114957090240874027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172330996153276120321165369 129248247114957090240874027)
      ·
        refine ⟨193872370672435635361311041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129248247114957090240874027 193872370672435635361311041)
        ·
          refine ⟨145404278004326726520983281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193872370672435635361311041 145404278004326726520983281)
          ·
            refine ⟨109053208503245044890737461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145404278004326726520983281 109053208503245044890737461)
            ·
              refine ⟨10223738297179222958506637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 109053208503245044890737461 10223738297179222958506637)
              ·
                refine ⟨3833901861442208609439989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10223738297179222958506637 3833901861442208609439989)
                ·
                  refine ⟨359428299510207057134999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3833901861442208609439989 359428299510207057134999)
                  ·
                    rfl

theorem cell23_6299857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 5, 3, 5].length) (baseStart_6299857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299857 prefixEnd_6299857 := by exact prefixLift 6299857
  have htrace : WordTrace (prefixWord ++ tailWord_6299857) baseStart_6299857 baseEnd_6299857 := by
    simpa [prefixWord, tailWord_6299857, baseEnd_6299857] using wordTrace_append hprefix tailTrace_6299857
  have hstable : (prefixWord ++ tailWord_6299857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299857).length < 2 ^ (prefixWord ++ tailWord_6299857).sum := by decide
  have hdescent : baseEnd_6299857 < baseStart_6299857 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299880 : List Nat := [2, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7]
def baseStart_6299880 : Nat := 118140960795 + 6299880 * 2 ^ 59
def prefixEnd_6299880 : Nat := 4983230072969 + 3 ^ 40 * 6299880 * 2
def baseEnd_6299880 : Nat := 3234866505646916924227385

theorem tailTrace_6299880 : CollatzResearch.WordTrace tailWord_6299880 prefixEnd_6299880 3234866505646916924227385 := by
  unfold tailWord_6299880
  simp only [CollatzResearch.WordTrace]
  refine ⟨114887750208309084344820547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153183666944412112459760729 114887750208309084344820547)
  ·
    refine ⟨172331625312463626517230821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114887750208309084344820547 172331625312463626517230821)
    ·
      refine ⟨32312179746086929971980779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172331625312463626517230821 32312179746086929971980779)
      ·
        refine ⟨48468269619130394957971169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32312179746086929971980779 48468269619130394957971169)
        ·
          refine ⟨36351202214347796218478377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48468269619130394957971169 36351202214347796218478377)
          ·
            refine ⟨27263401660760847163858783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36351202214347796218478377 27263401660760847163858783)
            ·
              refine ⟨40895102491141270745788175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27263401660760847163858783 40895102491141270745788175)
              ·
                refine ⟨61342653736711906118682263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40895102491141270745788175 61342653736711906118682263)
                ·
                  refine ⟨92013980605067859178023395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61342653736711906118682263 92013980605067859178023395)
                  ·
                    refine ⟨138020970907601788767035093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92013980605067859178023395 138020970907601788767035093)
                    ·
                      refine ⟨3234866505646916924227385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138020970907601788767035093 3234866505646916924227385)
                      ·
                        rfl

theorem cell23_6299880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 1, 1, 1, 7].length) (baseStart_6299880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299880 prefixEnd_6299880 := by exact prefixLift 6299880
  have htrace : WordTrace (prefixWord ++ tailWord_6299880) baseStart_6299880 baseEnd_6299880 := by
    simpa [prefixWord, tailWord_6299880, baseEnd_6299880] using wordTrace_append hprefix tailTrace_6299880
  have hstable : (prefixWord ++ tailWord_6299880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299880).length < 2 ^ (prefixWord ++ tailWord_6299880).sum := by decide
  have hdescent : baseEnd_6299880 < baseStart_6299880 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299885 : List Nat := [1, 5, 1, 2, 3, 2, 2, 1, 2, 2, 2]
def baseStart_6299885 : Nat := 118140960795 + 6299885 * 2 ^ 59
def prefixEnd_6299885 : Nat := 4983230072969 + 3 ^ 40 * 6299885 * 2
def baseEnd_6299885 : Nat := 3234869073050189404664863

theorem tailTrace_6299885 : CollatzResearch.WordTrace tailWord_6299885 prefixEnd_6299885 3234869073050189404664863 := by
  unfold tailWord_6299885
  simp only [CollatzResearch.WordTrace]
  refine ⟨229775682781600054543573109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153183788521066703029048739 229775682781600054543573109)
  ·
    refine ⟨21541470260775005113459979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229775682781600054543573109 21541470260775005113459979)
    ·
      refine ⟨32312205391162507670189969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21541470260775005113459979 32312205391162507670189969)
      ·
        refine ⟨24234154043371880752642477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32312205391162507670189969 24234154043371880752642477)
        ·
          refine ⟨9087807766264455282240929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24234154043371880752642477 9087807766264455282240929)
          ·
            refine ⟨6815855824698341461680697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9087807766264455282240929 6815855824698341461680697)
            ·
              refine ⟨5111891868523756096260523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6815855824698341461680697 5111891868523756096260523)
              ·
                refine ⟨7667837802785634144390785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5111891868523756096260523 7667837802785634144390785)
                ·
                  refine ⟨5750878352089225608293089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7667837802785634144390785 5750878352089225608293089)
                  ·
                    refine ⟨4313158764066919206219817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5750878352089225608293089 4313158764066919206219817)
                    ·
                      refine ⟨3234869073050189404664863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313158764066919206219817 3234869073050189404664863)
                      ·
                        rfl

theorem cell23_6299885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_6299885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299885 prefixEnd_6299885 := by exact prefixLift 6299885
  have htrace : WordTrace (prefixWord ++ tailWord_6299885) baseStart_6299885 baseEnd_6299885 := by
    simpa [prefixWord, tailWord_6299885, baseEnd_6299885] using wordTrace_append hprefix tailTrace_6299885
  have hstable : (prefixWord ++ tailWord_6299885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299885).length < 2 ^ (prefixWord ++ tailWord_6299885).sum := by decide
  have hdescent : baseEnd_6299885 < baseStart_6299885 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299907 : List Nat := [1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4]
def baseStart_6299907 : Nat := 118140960795 + 6299907 * 2 ^ 59
def prefixEnd_6299907 : Nat := 4983230072969 + 3 ^ 40 * 6299907 * 2
def baseEnd_6299907 : Nat := 3234880369624588318589761

theorem tailTrace_6299907 : CollatzResearch.WordTrace tailWord_6299907 prefixEnd_6299907 3234880369624588318589761 := by
  unfold tailWord_6299907
  simp only [CollatzResearch.WordTrace]
  refine ⟨229776485187520352300873975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153184323458346901533915983 229776485187520352300873975)
  ·
    refine ⟨344664727781280528451310963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229776485187520352300873975 344664727781280528451310963)
    ·
      refine ⟨516997091671920792676966445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344664727781280528451310963 516997091671920792676966445)
      ·
        refine ⟨193873909376970297253862417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 516997091671920792676966445 193873909376970297253862417)
        ·
          refine ⟨145405432032727722940396813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193873909376970297253862417 145405432032727722940396813)
          ·
            refine ⟨54527037012272896102648805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145405432032727722940396813 54527037012272896102648805)
            ·
              refine ⟨10223819439801168019246651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54527037012272896102648805 10223819439801168019246651)
              ·
                refine ⟨15335729159701752028869977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10223819439801168019246651 15335729159701752028869977)
                ·
                  refine ⟨11501796869776314021652483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15335729159701752028869977 11501796869776314021652483)
                  ·
                    refine ⟨17252695304664471032478725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11501796869776314021652483 17252695304664471032478725)
                    ·
                      refine ⟨3234880369624588318589761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17252695304664471032478725 3234880369624588318589761)
                      ·
                        rfl

theorem cell23_6299907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_6299907 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299907 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299907 prefixEnd_6299907 := by exact prefixLift 6299907
  have htrace : WordTrace (prefixWord ++ tailWord_6299907) baseStart_6299907 baseEnd_6299907 := by
    simpa [prefixWord, tailWord_6299907, baseEnd_6299907] using wordTrace_append hprefix tailTrace_6299907
  have hstable : (prefixWord ++ tailWord_6299907).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299907).length < 2 ^ (prefixWord ++ tailWord_6299907).sum := by decide
  have hdescent : baseEnd_6299907 < baseStart_6299907 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299961 : List Nat := [1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6299961 : Nat := 118140960795 + 6299961 * 2 ^ 59
def prefixEnd_6299961 : Nat := 4983230072969 + 3 ^ 40 * 6299961 * 2
def baseEnd_6299961 : Nat := 3234908097579931107314513

theorem tailTrace_6299961 : CollatzResearch.WordTrace tailWord_6299961 prefixEnd_6299961 3234908097579931107314513 := by
  unfold tailWord_6299961
  simp only [CollatzResearch.WordTrace]
  refine ⟨229778454729324719523339737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153185636486216479682226491 229778454729324719523339737)
  ·
    refine ⟨172333841046993539642504803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229778454729324719523339737 172333841046993539642504803)
    ·
      refine ⟨258500761570490309463757205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172333841046993539642504803 258500761570490309463757205)
      ·
        refine ⟨12117223198616733256113619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 258500761570490309463757205 12117223198616733256113619)
        ·
          refine ⟨18175834797925099884170429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12117223198616733256113619 18175834797925099884170429)
          ·
            refine ⟨6815938049221912456563911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18175834797925099884170429 6815938049221912456563911)
            ·
              refine ⟨10223907073832868684845867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6815938049221912456563911 10223907073832868684845867)
              ·
                refine ⟨15335860610749303027268801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10223907073832868684845867 15335860610749303027268801)
                ·
                  refine ⟨11501895458061977270451601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15335860610749303027268801 11501895458061977270451601)
                  ·
                    refine ⟨8626421593546482952838701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11501895458061977270451601 8626421593546482952838701)
                    ·
                      refine ⟨3234908097579931107314513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8626421593546482952838701 3234908097579931107314513)
                      ·
                        rfl

theorem cell23_6299961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6299961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299961 prefixEnd_6299961 := by exact prefixLift 6299961
  have htrace : WordTrace (prefixWord ++ tailWord_6299961) baseStart_6299961 baseEnd_6299961 := by
    simpa [prefixWord, tailWord_6299961, baseEnd_6299961] using wordTrace_append hprefix tailTrace_6299961
  have hstable : (prefixWord ++ tailWord_6299961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299961).length < 2 ^ (prefixWord ++ tailWord_6299961).sum := by decide
  have hdescent : baseEnd_6299961 < baseStart_6299961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6299991 : List Nat := [1, 1, 3, 2, 3, 1, 1, 6, 1, 1, 3]
def baseStart_6299991 : Nat := 118140960795 + 6299991 * 2 ^ 59
def prefixEnd_6299991 : Nat := 4983230072969 + 3 ^ 40 * 6299991 * 2
def baseEnd_6299991 : Nat := 3234923501999565989939375

theorem tailTrace_6299991 : CollatzResearch.WordTrace tailWord_6299991 prefixEnd_6299991 3234923501999565989939375 := by
  unfold tailWord_6299991
  simp only [CollatzResearch.WordTrace]
  refine ⟨229779548919216034646931827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153186365946144023097954551 229779548919216034646931827)
  ·
    refine ⟨344669323378824051970397741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229779548919216034646931827 344669323378824051970397741)
    ·
      refine ⟨129250996267059019488899153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344669323378824051970397741 129250996267059019488899153)
      ·
        refine ⟨96938247200294264616674365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129250996267059019488899153 96938247200294264616674365)
        ·
          refine ⟨36351842700110349231252887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96938247200294264616674365 36351842700110349231252887)
          ·
            refine ⟨54527764050165523846879331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36351842700110349231252887 54527764050165523846879331)
            ·
              refine ⟨81791646075248285770318997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54527764050165523846879331 81791646075248285770318997)
              ·
                refine ⟨3833983409777263395483703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81791646075248285770318997 3833983409777263395483703)
                ·
                  refine ⟨5750975114665895093225555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3833983409777263395483703 5750975114665895093225555)
                  ·
                    refine ⟨8626462671998842639838333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5750975114665895093225555 8626462671998842639838333)
                    ·
                      refine ⟨3234923501999565989939375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8626462671998842639838333 3234923501999565989939375)
                      ·
                        rfl

theorem cell23_6299991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 6, 1, 1, 3].length) (baseStart_6299991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6299991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6299991 prefixEnd_6299991 := by exact prefixLift 6299991
  have htrace : WordTrace (prefixWord ++ tailWord_6299991) baseStart_6299991 baseEnd_6299991 := by
    simpa [prefixWord, tailWord_6299991, baseEnd_6299991] using wordTrace_append hprefix tailTrace_6299991
  have hstable : (prefixWord ++ tailWord_6299991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6299991).length < 2 ^ (prefixWord ++ tailWord_6299991).sum := by decide
  have hdescent : baseEnd_6299991 < baseStart_6299991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6299991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300042 : List Nat := [3, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3]
def baseStart_6300042 : Nat := 118140960795 + 6300042 * 2 ^ 59
def prefixEnd_6300042 : Nat := 4983230072969 + 3 ^ 40 * 6300042 * 2
def baseEnd_6300042 : Nat := 3234949689512945290401641

theorem tailTrace_6300042 : CollatzResearch.WordTrace tailWord_6300042 prefixEnd_6300042 3234949689512945290401641 := by
  unfold tailWord_6300042
  simp only [CollatzResearch.WordTrace]
  refine ⟨57445352260507817589259595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153187606028020846904692253 57445352260507817589259595)
  ·
    refine ⟨86168028390761726383889393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57445352260507817589259595 86168028390761726383889393)
    ·
      refine ⟨64626021293071294787917045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86168028390761726383889393 64626021293071294787917045)
      ·
        refine ⟨6058689496225433886367223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64626021293071294787917045 6058689496225433886367223)
        ·
          refine ⟨9088034244338150829550835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058689496225433886367223 9088034244338150829550835)
          ·
            refine ⟨13632051366507226244326253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9088034244338150829550835 13632051366507226244326253)
            ·
              refine ⟨5112019262440209841622345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13632051366507226244326253 5112019262440209841622345)
              ·
                refine ⟨3834014446830157381216759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112019262440209841622345 3834014446830157381216759)
                ·
                  refine ⟨5751021670245236071825139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834014446830157381216759 5751021670245236071825139)
                  ·
                    refine ⟨8626532505367854107737709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5751021670245236071825139 8626532505367854107737709)
                    ·
                      refine ⟨3234949689512945290401641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8626532505367854107737709 3234949689512945290401641)
                      ·
                        rfl

theorem cell23_6300042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 2, 1, 1, 3].length) (baseStart_6300042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300042 prefixEnd_6300042 := by exact prefixLift 6300042
  have htrace : WordTrace (prefixWord ++ tailWord_6300042) baseStart_6300042 baseEnd_6300042 := by
    simpa [prefixWord, tailWord_6300042, baseEnd_6300042] using wordTrace_append hprefix tailTrace_6300042
  have hstable : (prefixWord ++ tailWord_6300042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300042).length < 2 ^ (prefixWord ++ tailWord_6300042).sum := by decide
  have hdescent : baseEnd_6300042 < baseStart_6300042 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300058 : List Nat := [3, 1, 1, 4, 1, 4, 2, 1, 2, 4]
def baseStart_6300058 : Nat := 118140960795 + 6300058 * 2 ^ 59
def prefixEnd_6300058 : Nat := 4983230072969 + 3 ^ 40 * 6300058 * 2
def baseEnd_6300058 : Nat := 1078319301734472409267189

theorem tailTrace_6300058 : CollatzResearch.WordTrace tailWord_6300058 prefixEnd_6300058 1078319301734472409267189 := by
  unfold tailWord_6300058
  simp only [CollatzResearch.WordTrace]
  refine ⟨57445498152493326272405207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153187995073315536726413885 57445498152493326272405207)
  ·
    refine ⟨86168247228739989408607811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57445498152493326272405207 86168247228739989408607811)
    ·
      refine ⟨129252370843109984112911717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86168247228739989408607811 129252370843109984112911717)
      ·
        refine ⟨24234819533083122021170947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 129252370843109984112911717 24234819533083122021170947)
        ·
          refine ⟨36352229299624683031756421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24234819533083122021170947 36352229299624683031756421)
          ·
            refine ⟨6816042993679628068454329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36352229299624683031756421 6816042993679628068454329)
            ·
              refine ⟨5112032245259721051340747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816042993679628068454329 5112032245259721051340747)
              ·
                refine ⟨7668048367889581577011121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112032245259721051340747 7668048367889581577011121)
                ·
                  refine ⟨5751036275917186182758341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668048367889581577011121 5751036275917186182758341)
                  ·
                    refine ⟨1078319301734472409267189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751036275917186182758341 1078319301734472409267189)
                    ·
                      rfl

theorem cell23_6300058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 4, 2, 1, 2, 4].length) (baseStart_6300058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300058 prefixEnd_6300058 := by exact prefixLift 6300058
  have htrace : WordTrace (prefixWord ++ tailWord_6300058) baseStart_6300058 baseEnd_6300058 := by
    simpa [prefixWord, tailWord_6300058, baseEnd_6300058] using wordTrace_append hprefix tailTrace_6300058
  have hstable : (prefixWord ++ tailWord_6300058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300058).length < 2 ^ (prefixWord ++ tailWord_6300058).sum := by decide
  have hdescent : baseEnd_6300058 < baseStart_6300058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300065 : List Nat := [1, 2, 3, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6300065 : Nat := 118140960795 + 6300065 * 2 ^ 59
def prefixEnd_6300065 : Nat := 4983230072969 + 3 ^ 40 * 6300065 * 2
def baseEnd_6300065 : Nat := 3234961499567998700414035

theorem tailTrace_6300065 : CollatzResearch.WordTrace tailWord_6300065 prefixEnd_6300065 3234961499567998700414035 := by
  unfold tailWord_6300065
  simp only [CollatzResearch.WordTrace]
  refine ⟨229782247920947945285125649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153188165280631963523417099 229782247920947945285125649)
  ·
    refine ⟨172336685940710958963844237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229782247920947945285125649 172336685940710958963844237)
    ·
      refine ⟨64626257227766609611441589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172336685940710958963844237 64626257227766609611441589)
      ·
        refine ⟨6058711615103119651072649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64626257227766609611441589 6058711615103119651072649)
        ·
          refine ⟨4544033711327339738304487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6058711615103119651072649 4544033711327339738304487)
          ·
            refine ⟨6816050566991009607456731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544033711327339738304487 6816050566991009607456731)
            ·
              refine ⟨10224075850486514411185097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816050566991009607456731 10224075850486514411185097)
              ·
                refine ⟨7668056887864885808388823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10224075850486514411185097 7668056887864885808388823)
                ·
                  refine ⟨11502085331797328712583235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7668056887864885808388823 11502085331797328712583235)
                  ·
                    refine ⟨17253127997695993068874853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11502085331797328712583235 17253127997695993068874853)
                    ·
                      refine ⟨3234961499567998700414035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17253127997695993068874853 3234961499567998700414035)
                      ·
                        rfl

theorem cell23_6300065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6300065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300065 prefixEnd_6300065 := by exact prefixLift 6300065
  have htrace : WordTrace (prefixWord ++ tailWord_6300065) baseStart_6300065 baseEnd_6300065 := by
    simpa [prefixWord, tailWord_6300065, baseEnd_6300065] using wordTrace_append hprefix tailTrace_6300065
  have hstable : (prefixWord ++ tailWord_6300065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300065).length < 2 ^ (prefixWord ++ tailWord_6300065).sum := by decide
  have hdescent : baseEnd_6300065 < baseStart_6300065 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300121 : List Nat := [1, 2, 1, 2, 4, 1, 4, 1, 1, 4, 2]
def baseStart_6300121 : Nat := 118140960795 + 6300121 * 2 ^ 59
def prefixEnd_6300121 : Nat := 4983230072969 + 3 ^ 40 * 6300121 * 2
def baseEnd_6300121 : Nat := 3234990254484650481313777

theorem tailTrace_6300121 : CollatzResearch.WordTrace tailWord_6300121 prefixEnd_6300121 3234990254484650481313777 := by
  unfold tailWord_6300121
  simp only [CollatzResearch.WordTrace]
  refine ⟨229784290408745066849164217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153189526939163377899442811 229784290408745066849164217)
  ·
    refine ⟨172338217806558800136873163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229784290408745066849164217 172338217806558800136873163)
    ·
      refine ⟨258507326709838200205309745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172338217806558800136873163 258507326709838200205309745)
      ·
        refine ⟨193880495032378650153982309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258507326709838200205309745 193880495032378650153982309)
        ·
          refine ⟨36352592818570996903871683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193880495032378650153982309 36352592818570996903871683)
          ·
            refine ⟨54528889227856495355807525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36352592818570996903871683 54528889227856495355807525)
            ·
              refine ⟨10224166730223092879213911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54528889227856495355807525 10224166730223092879213911)
              ·
                refine ⟨15336250095334639318820867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224166730223092879213911 15336250095334639318820867)
                ·
                  refine ⟨23004375143001958978231301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15336250095334639318820867 23004375143001958978231301)
                  ·
                    refine ⟨4313320339312867308418369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23004375143001958978231301 4313320339312867308418369)
                    ·
                      refine ⟨3234990254484650481313777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313320339312867308418369 3234990254484650481313777)
                      ·
                        rfl

theorem cell23_6300121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 4, 2].length) (baseStart_6300121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300121 prefixEnd_6300121 := by exact prefixLift 6300121
  have htrace : WordTrace (prefixWord ++ tailWord_6300121) baseStart_6300121 baseEnd_6300121 := by
    simpa [prefixWord, tailWord_6300121, baseEnd_6300121] using wordTrace_append hprefix tailTrace_6300121
  have hstable : (prefixWord ++ tailWord_6300121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300121).length < 2 ^ (prefixWord ++ tailWord_6300121).sum := by decide
  have hdescent : baseEnd_6300121 < baseStart_6300121 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300127 : List Nat := [1, 1, 2, 3, 3, 2, 1, 1, 9]
def baseStart_6300127 : Nat := 118140960795 + 6300127 * 2 ^ 59
def prefixEnd_6300127 : Nat := 4983230072969 + 3 ^ 40 * 6300127 * 2
def baseEnd_6300127 : Nat := 359443703929841939759861

theorem tailTrace_6300127 : CollatzResearch.WordTrace tailWord_6300127 prefixEnd_6300127 359443703929841939759861 := by
  unfold tailWord_6300127
  simp only [CollatzResearch.WordTrace]
  refine ⟨229784509246723329873882635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153189672831148886582588423 229784509246723329873882635)
  ·
    refine ⟨344676763870084994810823953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229784509246723329873882635 344676763870084994810823953)
    ·
      refine ⟨258507572902563746108117965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344676763870084994810823953 258507572902563746108117965)
      ·
        refine ⟨96940339838461404790544237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258507572902563746108117965 96940339838461404790544237)
        ·
          refine ⟨36352627439423026796454089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96940339838461404790544237 36352627439423026796454089)
          ·
            refine ⟨27264470579567270097340567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36352627439423026796454089 27264470579567270097340567)
            ·
              refine ⟨40896705869350905146010851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27264470579567270097340567 40896705869350905146010851)
              ·
                refine ⟨61345058804026357719016277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40896705869350905146010851 61345058804026357719016277)
                ·
                  refine ⟨359443703929841939759861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61345058804026357719016277 359443703929841939759861)
                  ·
                    rfl

theorem cell23_6300127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 2, 1, 1, 9].length) (baseStart_6300127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300127 prefixEnd_6300127 := by exact prefixLift 6300127
  have htrace : WordTrace (prefixWord ++ tailWord_6300127) baseStart_6300127 baseEnd_6300127 := by
    simpa [prefixWord, tailWord_6300127, baseEnd_6300127] using wordTrace_append hprefix tailTrace_6300127
  have hstable : (prefixWord ++ tailWord_6300127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300127).length < 2 ^ (prefixWord ++ tailWord_6300127).sum := by decide
  have hdescent : baseEnd_6300127 < baseStart_6300127 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300161 : List Nat := [1, 2, 4, 1, 3, 1, 2, 4, 5]
def baseStart_6300161 : Nat := 118140960795 + 6300161 * 2 ^ 59
def prefixEnd_6300161 : Nat := 4983230072969 + 3 ^ 40 * 6300161 * 2
def baseEnd_6300161 : Nat := 359445643745647813868177

theorem tailTrace_6300161 : CollatzResearch.WordTrace tailWord_6300161 prefixEnd_6300161 359445643745647813868177 := by
  unfold tailWord_6300161
  simp only [CollatzResearch.WordTrace]
  refine ⟨229785749328600153680620337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153190499552400102453746891 229785749328600153680620337)
  ·
    refine ⟨172339311996450115260465253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229785749328600153680620337 172339311996450115260465253)
    ·
      refine ⟨32313620999334396611337235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172339311996450115260465253 32313620999334396611337235)
      ·
        refine ⟨48470431499001594917005853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32313620999334396611337235 48470431499001594917005853)
        ·
          refine ⟨18176411812125598093877195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48470431499001594917005853 18176411812125598093877195)
          ·
            refine ⟨27264617718188397140815793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18176411812125598093877195 27264617718188397140815793)
            ·
              refine ⟨20448463288641297855611845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27264617718188397140815793 20448463288641297855611845)
              ·
                refine ⟨3834086866620243347927221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20448463288641297855611845 3834086866620243347927221)
                ·
                  refine ⟨359445643745647813868177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3834086866620243347927221 359445643745647813868177)
                  ·
                    rfl

theorem cell23_6300161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 2, 4, 5].length) (baseStart_6300161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300161 prefixEnd_6300161 := by exact prefixLift 6300161
  have htrace : WordTrace (prefixWord ++ tailWord_6300161) baseStart_6300161 baseEnd_6300161 := by
    simpa [prefixWord, tailWord_6300161, baseEnd_6300161] using wordTrace_append hprefix tailTrace_6300161
  have hstable : (prefixWord ++ tailWord_6300161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300161).length < 2 ^ (prefixWord ++ tailWord_6300161).sum := by decide
  have hdescent : baseEnd_6300161 < baseStart_6300161 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300174 : List Nat := [4, 1, 1, 2, 3, 1, 1, 2, 1, 7]
def baseStart_6300174 : Nat := 118140960795 + 6300174 * 2 ^ 59
def prefixEnd_6300174 : Nat := 4983230072969 + 3 ^ 40 * 6300174 * 2
def baseEnd_6300174 : Nat := 1078339156319779591317011

theorem tailTrace_6300174 : CollatzResearch.WordTrace tailWord_6300174 prefixEnd_6300174 1078339156319779591317011 := by
  unfold tailWord_6300174
  simp only [CollatzResearch.WordTrace]
  refine ⟨28723277934694132112605447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153190815651702037933895717 28723277934694132112605447)
  ·
    refine ⟨43084916902041198168908171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28723277934694132112605447 43084916902041198168908171)
    ·
      refine ⟨64627375353061797253362257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43084916902041198168908171 64627375353061797253362257)
      ·
        refine ⟨48470531514796347940021693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64627375353061797253362257 48470531514796347940021693)
        ·
          refine ⟨18176449318048630477508135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48470531514796347940021693 18176449318048630477508135)
          ·
            refine ⟨27264673977072945716262203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18176449318048630477508135 27264673977072945716262203)
            ·
              refine ⟨40897010965609418574393305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27264673977072945716262203 40897010965609418574393305)
              ·
                refine ⟨30672758224207063930794979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40897010965609418574393305 30672758224207063930794979)
                ·
                  refine ⟨46009137336310595896192469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30672758224207063930794979 46009137336310595896192469)
                  ·
                    refine ⟨1078339156319779591317011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46009137336310595896192469 1078339156319779591317011)
                    ·
                      rfl

theorem cell23_6300174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 1, 2, 1, 7].length) (baseStart_6300174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300174 prefixEnd_6300174 := by exact prefixLift 6300174
  have htrace : WordTrace (prefixWord ++ tailWord_6300174) baseStart_6300174 baseEnd_6300174 := by
    simpa [prefixWord, tailWord_6300174, baseEnd_6300174] using wordTrace_append hprefix tailTrace_6300174
  have hstable : (prefixWord ++ tailWord_6300174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300174).length < 2 ^ (prefixWord ++ tailWord_6300174).sum := by decide
  have hdescent : baseEnd_6300174 < baseStart_6300174 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300204 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 5, 4]
def baseStart_6300204 : Nat := 118140960795 + 6300204 * 2 ^ 59
def prefixEnd_6300204 : Nat := 4983230072969 + 3 ^ 40 * 6300204 * 2
def baseEnd_6300204 : Nat := 1078344291126324552191965

theorem tailTrace_6300204 : CollatzResearch.WordTrace tailWord_6300204 prefixEnd_6300204 1078344291126324552191965 := by
  unfold tailWord_6300204
  simp only [CollatzResearch.WordTrace]
  refine ⟨114893658833722186012217833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153191545111629581349623777 114893658833722186012217833)
  ·
    refine ⟨86170244125291639509163375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114893658833722186012217833 86170244125291639509163375)
    ·
      refine ⟨129255366187937459263745063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86170244125291639509163375 129255366187937459263745063)
      ·
        refine ⟨193883049281906188895617595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129255366187937459263745063 193883049281906188895617595)
        ·
          refine ⟨290824573922859283343426393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193883049281906188895617595 290824573922859283343426393)
          ·
            refine ⟨218118430442144462507569795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290824573922859283343426393 218118430442144462507569795)
            ·
              refine ⟨327177645663216693761354693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218118430442144462507569795 327177645663216693761354693)
              ·
                refine ⟨61345808561853130080254005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 327177645663216693761354693 61345808561853130080254005)
                ·
                  refine ⟨5751169552673730945023813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61345808561853130080254005 5751169552673730945023813)
                  ·
                    refine ⟨1078344291126324552191965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751169552673730945023813 1078344291126324552191965)
                    ·
                      rfl

theorem cell23_6300204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 4].length) (baseStart_6300204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300204 prefixEnd_6300204 := by exact prefixLift 6300204
  have htrace : WordTrace (prefixWord ++ tailWord_6300204) baseStart_6300204 baseEnd_6300204 := by
    simpa [prefixWord, tailWord_6300204, baseEnd_6300204] using wordTrace_append hprefix tailTrace_6300204
  have hstable : (prefixWord ++ tailWord_6300204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300204).length < 2 ^ (prefixWord ++ tailWord_6300204).sum := by decide
  have hdescent : baseEnd_6300204 < baseStart_6300204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300212 : List Nat := [2, 5, 1, 3, 1, 1, 3, 2, 5]
def baseStart_6300212 : Nat := 118140960795 + 6300212 * 2 ^ 59
def prefixEnd_6300212 : Nat := 4983230072969 + 3 ^ 40 * 6300212 * 2
def baseEnd_6300212 : Nat := 359448553469356625030651

theorem tailTrace_6300212 : CollatzResearch.WordTrace tailWord_6300212 prefixEnd_6300212 359448553469356625030651 := by
  unfold tailWord_6300212
  simp only [CollatzResearch.WordTrace]
  refine ⟨114893804725707694695363445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153191739634276926260484593 114893804725707694695363445)
  ·
    refine ⟨10771294193035096377690323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 114893804725707694695363445 10771294193035096377690323)
    ·
      refine ⟨16156941289552644566535485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771294193035096377690323 16156941289552644566535485)
      ·
        refine ⟨6058852983582241712450807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16156941289552644566535485 6058852983582241712450807)
        ·
          refine ⟨9088279475373362568676211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6058852983582241712450807 9088279475373362568676211)
          ·
            refine ⟨13632419213060043853014317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9088279475373362568676211 13632419213060043853014317)
            ·
              refine ⟨5112157204897516444880369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13632419213060043853014317 5112157204897516444880369)
              ·
                refine ⟨3834117903673137333660277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112157204897516444880369 3834117903673137333660277)
                ·
                  refine ⟨359448553469356625030651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3834117903673137333660277 359448553469356625030651)
                  ·
                    rfl

theorem cell23_6300212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 3, 1, 1, 3, 2, 5].length) (baseStart_6300212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300212 prefixEnd_6300212 := by exact prefixLift 6300212
  have htrace : WordTrace (prefixWord ++ tailWord_6300212) baseStart_6300212 baseEnd_6300212 := by
    simpa [prefixWord, tailWord_6300212, baseEnd_6300212] using wordTrace_append hprefix tailTrace_6300212
  have hstable : (prefixWord ++ tailWord_6300212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300212).length < 2 ^ (prefixWord ++ tailWord_6300212).sum := by decide
  have hdescent : baseEnd_6300212 < baseStart_6300212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300272 : List Nat := [2, 1, 1, 1, 7, 2, 2, 2, 1, 4]
def baseStart_6300272 : Nat := 118140960795 + 6300272 * 2 ^ 59
def prefixEnd_6300272 : Nat := 4983230072969 + 3 ^ 40 * 6300272 * 2
def baseEnd_6300272 : Nat := 1078355930021159796841861

theorem tailTrace_6300272 : CollatzResearch.WordTrace tailWord_6300272 prefixEnd_6300272 1078355930021159796841861 := by
  unfold tailWord_6300272
  simp only [CollatzResearch.WordTrace]
  refine ⟨114894898915599009818955535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153193198554132013091940713 114894898915599009818955535)
  ·
    refine ⟨172342348373398514728433303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114894898915599009818955535 172342348373398514728433303)
    ·
      refine ⟨258513522560097772092649955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172342348373398514728433303 258513522560097772092649955)
      ·
        refine ⟨387770283840146658138974933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258513522560097772092649955 387770283840146658138974933)
        ·
          refine ⟨9088366027503437300132225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 387770283840146658138974933 9088366027503437300132225)
          ·
            refine ⟨6816274520627577975099169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9088366027503437300132225 6816274520627577975099169)
            ·
              refine ⟨5112205890470683481324377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6816274520627577975099169 5112205890470683481324377)
              ·
                refine ⟨3834154417853012610993283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5112205890470683481324377 3834154417853012610993283)
                ·
                  refine ⟨5751231626779518916489925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834154417853012610993283 5751231626779518916489925)
                  ·
                    refine ⟨1078355930021159796841861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751231626779518916489925 1078355930021159796841861)
                    ·
                      rfl

theorem cell23_6300272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 2, 1, 4].length) (baseStart_6300272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300272 prefixEnd_6300272 := by exact prefixLift 6300272
  have htrace : WordTrace (prefixWord ++ tailWord_6300272) baseStart_6300272 baseEnd_6300272 := by
    simpa [prefixWord, tailWord_6300272, baseEnd_6300272] using wordTrace_append hprefix tailTrace_6300272
  have hstable : (prefixWord ++ tailWord_6300272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300272).length < 2 ^ (prefixWord ++ tailWord_6300272).sum := by decide
  have hdescent : baseEnd_6300272 < baseStart_6300272 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300311 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 4, 4]
def baseStart_6300311 : Nat := 118140960795 + 6300311 * 2 ^ 59
def prefixEnd_6300311 : Nat := 4983230072969 + 3 ^ 40 * 6300311 * 2
def baseEnd_6300311 : Nat := 1078362605269668245979301

theorem tailTrace_6300311 : CollatzResearch.WordTrace tailWord_6300311 prefixEnd_6300311 1078362605269668245979301 := by
  unfold tailWord_6300311
  simp only [CollatzResearch.WordTrace]
  refine ⟨229791220278056729298580787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153194146852037819532387191 229791220278056729298580787)
  ·
    refine ⟨344686830417085093947871181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229791220278056729298580787 344686830417085093947871181)
    ·
      refine ⟨129257561406406910230451693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344686830417085093947871181 129257561406406910230451693)
      ·
        refine ⟨48471585527402591336419385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129257561406406910230451693 48471585527402591336419385)
        ·
          refine ⟨36353689145551943502314539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48471585527402591336419385 36353689145551943502314539)
          ·
            refine ⟨54530533718327915253471809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36353689145551943502314539 54530533718327915253471809)
            ·
              refine ⟨40897900288745936440103857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54530533718327915253471809 40897900288745936440103857)
              ·
                refine ⟨30673425216559452330077893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40897900288745936440103857 30673425216559452330077893)
                ·
                  refine ⟨5751267228104897311889605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30673425216559452330077893 5751267228104897311889605)
                  ·
                    refine ⟨1078362605269668245979301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751267228104897311889605 1078362605269668245979301)
                    ·
                      rfl

theorem cell23_6300311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 4, 4].length) (baseStart_6300311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300311 prefixEnd_6300311 := by exact prefixLift 6300311
  have htrace : WordTrace (prefixWord ++ tailWord_6300311) baseStart_6300311 baseEnd_6300311 := by
    simpa [prefixWord, tailWord_6300311, baseEnd_6300311] using wordTrace_append hprefix tailTrace_6300311
  have hstable : (prefixWord ++ tailWord_6300311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300311).length < 2 ^ (prefixWord ++ tailWord_6300311).sum := by decide
  have hdescent : baseEnd_6300311 < baseStart_6300311 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300324 : List Nat := [2, 3, 1, 2, 2, 1, 12]
def baseStart_6300324 : Nat := 118140960795 + 6300324 * 2 ^ 59
def prefixEnd_6300324 : Nat := 4983230072969 + 3 ^ 40 * 6300324 * 2
def baseEnd_6300324 : Nat := 39939438161203866507103

theorem tailTrace_6300324 : CollatzResearch.WordTrace tailWord_6300324 prefixEnd_6300324 39939438161203866507103 := by
  unfold tailWord_6300324
  simp only [CollatzResearch.WordTrace]
  refine ⟨114895847213504816259402013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153194462951339755012536017 114895847213504816259402013)
  ·
    refine ⟨43085942705064306097275755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114895847213504816259402013 43085942705064306097275755)
    ·
      refine ⟨64628914057596459145913633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43085942705064306097275755 64628914057596459145913633)
      ·
        refine ⟨48471685543197344359435225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64628914057596459145913633 48471685543197344359435225)
        ·
          refine ⟨36353764157398008269576419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48471685543197344359435225 36353764157398008269576419)
          ·
            refine ⟨54530646236097012404364629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36353764157398008269576419 54530646236097012404364629)
            ·
              refine ⟨39939438161203866507103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 54530646236097012404364629 39939438161203866507103)
              ·
                rfl

theorem cell23_6300324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 12].length) (baseStart_6300324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300324 prefixEnd_6300324 := by exact prefixLift 6300324
  have htrace : WordTrace (prefixWord ++ tailWord_6300324) baseStart_6300324 baseEnd_6300324 := by
    simpa [prefixWord, tailWord_6300324, baseEnd_6300324] using wordTrace_append hprefix tailTrace_6300324
  have hstable : (prefixWord ++ tailWord_6300324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300324).length < 2 ^ (prefixWord ++ tailWord_6300324).sum := by decide
  have hdescent : baseEnd_6300324 < baseStart_6300324 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300335 : List Nat := [1, 1, 2, 1, 2, 6, 2, 1, 3, 2, 2]
def baseStart_6300335 : Nat := 118140960795 + 6300335 * 2 ^ 59
def prefixEnd_6300335 : Nat := 4983230072969 + 3 ^ 40 * 6300335 * 2
def baseEnd_6300335 : Nat := 3235100139344712644037793

theorem tailTrace_6300335 : CollatzResearch.WordTrace tailWord_6300335 prefixEnd_6300335 3235100139344712644037793 := by
  unfold tailWord_6300335
  simp only [CollatzResearch.WordTrace]
  refine ⟨229792095629969781397454459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153194730419979854264969639 229792095629969781397454459)
  ·
    refine ⟨344688143444954672096181689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229792095629969781397454459 344688143444954672096181689)
    ·
      refine ⟨258516107583716004072136267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344688143444954672096181689 258516107583716004072136267)
      ·
        refine ⟨387774161375574006108204401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258516107583716004072136267 387774161375574006108204401)
        ·
          refine ⟨290830621031680504581153301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387774161375574006108204401 290830621031680504581153301)
          ·
            refine ⟨13632685360860023652241561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290830621031680504581153301 13632685360860023652241561)
            ·
              refine ⟨10224514020645017739181171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13632685360860023652241561 10224514020645017739181171)
              ·
                refine ⟨15336771030967526608771757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10224514020645017739181171 15336771030967526608771757)
                ·
                  refine ⟨5751289136612822478289409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15336771030967526608771757 5751289136612822478289409)
                  ·
                    refine ⟨4313466852459616858717057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751289136612822478289409 4313466852459616858717057)
                    ·
                      refine ⟨3235100139344712644037793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313466852459616858717057 3235100139344712644037793)
                      ·
                        rfl

theorem cell23_6300335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 1, 3, 2, 2].length) (baseStart_6300335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300335 prefixEnd_6300335 := by exact prefixLift 6300335
  have htrace : WordTrace (prefixWord ++ tailWord_6300335) baseStart_6300335 baseEnd_6300335 := by
    simpa [prefixWord, tailWord_6300335, baseEnd_6300335] using wordTrace_append hprefix tailTrace_6300335
  have hstable : (prefixWord ++ tailWord_6300335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300335).length < 2 ^ (prefixWord ++ tailWord_6300335).sum := by decide
  have hdescent : baseEnd_6300335 < baseStart_6300335 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300361 : List Nat := [1, 2, 1, 1, 2, 1, 1, 1, 4, 7, 2]
def baseStart_6300361 : Nat := 118140960795 + 6300361 * 2 ^ 59
def prefixEnd_6300361 : Nat := 4983230072969 + 3 ^ 40 * 6300361 * 2
def baseEnd_6300361 : Nat := 3235113489841729542312673

theorem tailTrace_6300361 : CollatzResearch.WordTrace tailWord_6300361 prefixEnd_6300361 3235113489841729542312673 := by
  unfold tailWord_6300361
  simp only [CollatzResearch.WordTrace]
  refine ⟨229793043927875587837900937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153195362618583725225267291 229793043927875587837900937)
  ·
    refine ⟨172344782945906690878425703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229793043927875587837900937 172344782945906690878425703)
    ·
      refine ⟨258517174418860036317638555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172344782945906690878425703 258517174418860036317638555)
      ·
        refine ⟨387775761628290054476457833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258517174418860036317638555 387775761628290054476457833)
        ·
          refine ⟨290831821221217540857343375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387775761628290054476457833 290831821221217540857343375)
          ·
            refine ⟨436247731831826311286015063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290831821221217540857343375 436247731831826311286015063)
            ·
              refine ⟨654371597747739466929022595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436247731831826311286015063 654371597747739466929022595)
              ·
                refine ⟨981557396621609200393533893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 654371597747739466929022595 981557396621609200393533893)
                ·
                  refine ⟨184042011866551725073787605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 981557396621609200393533893 184042011866551725073787605)
                  ·
                    refine ⟨4313484653122306056416897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 184042011866551725073787605 4313484653122306056416897)
                    ·
                      refine ⟨3235113489841729542312673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313484653122306056416897 3235113489841729542312673)
                      ·
                        rfl

theorem cell23_6300361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 7, 2].length) (baseStart_6300361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300361 prefixEnd_6300361 := by exact prefixLift 6300361
  have htrace : WordTrace (prefixWord ++ tailWord_6300361) baseStart_6300361 baseEnd_6300361 := by
    simpa [prefixWord, tailWord_6300361, baseEnd_6300361] using wordTrace_append hprefix tailTrace_6300361
  have hstable : (prefixWord ++ tailWord_6300361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300361).length < 2 ^ (prefixWord ++ tailWord_6300361).sum := by decide
  have hdescent : baseEnd_6300361 < baseStart_6300361 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300402 : List Nat := [3, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_6300402 : Nat := 118140960795 + 6300402 * 2 ^ 59
def prefixEnd_6300402 : Nat := 4983230072969 + 3 ^ 40 * 6300402 * 2
def baseEnd_6300402 : Nat := 3235134542548563881899985

theorem tailTrace_6300402 : CollatzResearch.WordTrace tailWord_6300402 prefixEnd_6300402 3235134542548563881899985 := by
  unfold tailWord_6300402
  simp only [CollatzResearch.WordTrace]
  refine ⟨57448634830181762960035865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153196359547151367893428973 57448634830181762960035865)
  ·
    refine ⟨43086476122636322220026899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57448634830181762960035865 43086476122636322220026899)
    ·
      refine ⟨64629714183954483330040349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43086476122636322220026899 64629714183954483330040349)
      ·
        refine ⟨24236142818982931248765131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64629714183954483330040349 24236142818982931248765131)
        ·
          refine ⟨36354214228474396873147697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24236142818982931248765131 36354214228474396873147697)
          ·
            refine ⟨27265660671355797654860773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36354214228474396873147697 27265660671355797654860773)
            ·
              refine ⟨5112311375879212060286395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27265660671355797654860773 5112311375879212060286395)
              ·
                refine ⟨7668467063818818090429593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112311375879212060286395 7668467063818818090429593)
                ·
                  refine ⟨5751350297864113567822195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668467063818818090429593 5751350297864113567822195)
                  ·
                    refine ⟨8627025446796170351733293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5751350297864113567822195 8627025446796170351733293)
                    ·
                      refine ⟨3235134542548563881899985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8627025446796170351733293 3235134542548563881899985)
                      ·
                        rfl

theorem cell23_6300402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_6300402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300402 prefixEnd_6300402 := by exact prefixLift 6300402
  have htrace : WordTrace (prefixWord ++ tailWord_6300402) baseStart_6300402 baseEnd_6300402 := by
    simpa [prefixWord, tailWord_6300402, baseEnd_6300402] using wordTrace_append hprefix tailTrace_6300402
  have hstable : (prefixWord ++ tailWord_6300402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300402).length < 2 ^ (prefixWord ++ tailWord_6300402).sum := by decide
  have hdescent : baseEnd_6300402 < baseStart_6300402 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300408 : List Nat := [2, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2]
def baseStart_6300408 : Nat := 118140960795 + 6300408 * 2 ^ 59
def prefixEnd_6300408 : Nat := 4983230072969 + 3 ^ 40 * 6300408 * 2
def baseEnd_6300408 : Nat := 3235137623432490858424957

theorem tailTrace_6300408 : CollatzResearch.WordTrace tailWord_6300408 prefixEnd_6300408 3235137623432490858424957 := by
  unfold tailWord_6300408
  simp only [CollatzResearch.WordTrace]
  refine ⟨114897379079352657432430939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153196505439136876576574585 114897379079352657432430939)
  ·
    refine ⟨172346068619028986148646409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114897379079352657432430939 172346068619028986148646409)
    ·
      refine ⟨129259551464271739611484807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172346068619028986148646409 129259551464271739611484807)
      ·
        refine ⟨193889327196407609417227211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129259551464271739611484807 193889327196407609417227211)
        ·
          refine ⟨290833990794611414125840817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193889327196407609417227211 290833990794611414125840817)
          ·
            refine ⟨218125493095958560594380613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290833990794611414125840817 218125493095958560594380613)
            ·
              refine ⟨40898529955492230111446365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218125493095958560594380613 40898529955492230111446365)
              ·
                refine ⟨15336948733309586291792387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40898529955492230111446365 15336948733309586291792387)
                ·
                  refine ⟨23005423099964379437688581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15336948733309586291792387 23005423099964379437688581)
                  ·
                    refine ⟨4313516831243321144566609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23005423099964379437688581 4313516831243321144566609)
                    ·
                      refine ⟨3235137623432490858424957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313516831243321144566609 3235137623432490858424957)
                      ·
                        rfl

theorem cell23_6300408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 3, 1, 4, 2].length) (baseStart_6300408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300408 prefixEnd_6300408 := by exact prefixLift 6300408
  have htrace : WordTrace (prefixWord ++ tailWord_6300408) baseStart_6300408 baseEnd_6300408 := by
    simpa [prefixWord, tailWord_6300408, baseEnd_6300408] using wordTrace_append hprefix tailTrace_6300408
  have hstable : (prefixWord ++ tailWord_6300408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300408).length < 2 ^ (prefixWord ++ tailWord_6300408).sum := by decide
  have hdescent : baseEnd_6300408 < baseStart_6300408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300412 : List Nat := [2, 2, 2, 1, 3, 4, 1, 2, 1, 3, 2]
def baseStart_6300412 : Nat := 118140960795 + 6300412 * 2 ^ 59
def prefixEnd_6300412 : Nat := 4983230072969 + 3 ^ 40 * 6300412 * 2
def baseEnd_6300412 : Nat := 3235139677355108842774939

theorem tailTrace_6300412 : CollatzResearch.WordTrace tailWord_6300412 prefixEnd_6300412 3235139677355108842774939 := by
  unfold tailWord_6300412
  simp only [CollatzResearch.WordTrace]
  refine ⟨114897452025345411774003745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153196602700460549032004993 114897452025345411774003745)
  ·
    refine ⟨86173089019009058830502809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114897452025345411774003745 86173089019009058830502809)
    ·
      refine ⟨64629816764256794122877107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86173089019009058830502809 64629816764256794122877107)
      ·
        refine ⟨96944725146385191184315661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64629816764256794122877107 96944725146385191184315661)
        ·
          refine ⟨36354271929894446694118373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 96944725146385191184315661 36354271929894446694118373)
          ·
            refine ⟨6816425986855208755147195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36354271929894446694118373 6816425986855208755147195)
            ·
              refine ⟨10224638980282813132720793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816425986855208755147195 10224638980282813132720793)
              ·
                refine ⟨7668479235212109849540595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10224638980282813132720793 7668479235212109849540595)
                ·
                  refine ⟨11502718852818164774310893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7668479235212109849540595 11502718852818164774310893)
                  ·
                    refine ⟨4313519569806811790366585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11502718852818164774310893 4313519569806811790366585)
                    ·
                      refine ⟨3235139677355108842774939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313519569806811790366585 3235139677355108842774939)
                      ·
                        rfl

theorem cell23_6300412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 2, 1, 3, 2].length) (baseStart_6300412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300412 prefixEnd_6300412 := by exact prefixLift 6300412
  have htrace : WordTrace (prefixWord ++ tailWord_6300412) baseStart_6300412 baseEnd_6300412 := by
    simpa [prefixWord, tailWord_6300412, baseEnd_6300412] using wordTrace_append hprefix tailTrace_6300412
  have hstable : (prefixWord ++ tailWord_6300412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300412).length < 2 ^ (prefixWord ++ tailWord_6300412).sum := by decide
  have hdescent : baseEnd_6300412 < baseStart_6300412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300442 : List Nat := [3, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2]
def baseStart_6300442 : Nat := 118140960795 + 6300442 * 2 ^ 59
def prefixEnd_6300442 : Nat := 4983230072969 + 3 ^ 40 * 6300442 * 2
def baseEnd_6300442 : Nat := 3235155081774743725399801

theorem tailTrace_6300442 : CollatzResearch.WordTrace tailWord_6300442 prefixEnd_6300442 3235155081774743725399801 := by
  unfold tailWord_6300442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57448999560145534667899895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153197332160388092447733053 57448999560145534667899895)
  ·
    refine ⟨86173499340218302001849843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57448999560145534667899895 86173499340218302001849843)
    ·
      refine ⟨129260249010327453002774765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86173499340218302001849843 129260249010327453002774765)
      ·
        refine ⟨48472593378872794876040537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129260249010327453002774765 48472593378872794876040537)
        ·
          refine ⟨36354445034154596157030403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48472593378872794876040537 36354445034154596157030403)
          ·
            refine ⟨54531667551231894235545605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36354445034154596157030403 54531667551231894235545605)
            ·
              refine ⟨10224687665855980169164801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54531667551231894235545605 10224687665855980169164801)
              ·
                refine ⟨7668515749391985126873601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10224687665855980169164801 7668515749391985126873601)
                ·
                  refine ⟨5751386812043988845155201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668515749391985126873601 5751386812043988845155201)
                  ·
                    refine ⟨4313540109032991633866401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751386812043988845155201 4313540109032991633866401)
                    ·
                      refine ⟨3235155081774743725399801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313540109032991633866401 3235155081774743725399801)
                      ·
                        rfl

theorem cell23_6300442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 4, 2, 2, 2, 2].length) (baseStart_6300442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300442 prefixEnd_6300442 := by exact prefixLift 6300442
  have htrace : WordTrace (prefixWord ++ tailWord_6300442) baseStart_6300442 baseEnd_6300442 := by
    simpa [prefixWord, tailWord_6300442, baseEnd_6300442] using wordTrace_append hprefix tailTrace_6300442
  have hstable : (prefixWord ++ tailWord_6300442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300442).length < 2 ^ (prefixWord ++ tailWord_6300442).sum := by decide
  have hdescent : baseEnd_6300442 < baseStart_6300442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300493 : List Nat := [1, 6, 1, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_6300493 : Nat := 118140960795 + 6300493 * 2 ^ 59
def prefixEnd_6300493 : Nat := 4983230072969 + 3 ^ 40 * 6300493 * 2
def baseEnd_6300493 : Nat := 3235181269288123025862067

theorem tailTrace_6300493 : CollatzResearch.WordTrace tailWord_6300493 prefixEnd_6300493 3235181269288123025862067 := by
  unfold tailWord_6300493
  simp only [CollatzResearch.WordTrace]
  refine ⟨229797858363397374381706133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153198572242264916254470755 229797858363397374381706133)
  ·
    refine ⟨10771774610784251924142475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229797858363397374381706133 10771774610784251924142475)
    ·
      refine ⟨16157661916176377886213713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10771774610784251924142475 16157661916176377886213713)
      ·
        refine ⟨12118246437132283414660285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16157661916176377886213713 12118246437132283414660285)
        ·
          refine ⟨4544342413924606280497607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12118246437132283414660285 4544342413924606280497607)
          ·
            refine ⟨6816513620886909420746411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544342413924606280497607 6816513620886909420746411)
            ·
              refine ⟨10224770431330364131119617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816513620886909420746411 10224770431330364131119617)
              ·
                refine ⟨7668577823497773098339713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10224770431330364131119617 7668577823497773098339713)
                ·
                  refine ⟨5751433367623329823754785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668577823497773098339713 5751433367623329823754785)
                  ·
                    refine ⟨4313575025717497367816089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751433367623329823754785 4313575025717497367816089)
                    ·
                      refine ⟨3235181269288123025862067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313575025717497367816089 3235181269288123025862067)
                      ·
                        rfl

theorem cell23_6300493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_6300493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300493 prefixEnd_6300493 := by exact prefixLift 6300493
  have htrace : WordTrace (prefixWord ++ tailWord_6300493) baseStart_6300493 baseEnd_6300493 := by
    simpa [prefixWord, tailWord_6300493, baseEnd_6300493] using wordTrace_append hprefix tailTrace_6300493
  have hstable : (prefixWord ++ tailWord_6300493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300493).length < 2 ^ (prefixWord ++ tailWord_6300493).sum := by decide
  have hdescent : baseEnd_6300493 < baseStart_6300493 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300498 : List Nat := [3, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_6300498 : Nat := 118140960795 + 6300498 * 2 ^ 59
def prefixEnd_6300498 : Nat := 4983230072969 + 3 ^ 40 * 6300498 * 2
def baseEnd_6300498 : Nat := 3235183836691395506299543

theorem tailTrace_6300498 : CollatzResearch.WordTrace tailWord_6300498 prefixEnd_6300498 3235183836691395506299543 := by
  unfold tailWord_6300498
  simp only [CollatzResearch.WordTrace]
  refine ⟨57449510182094815058909537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153198693818919506823758765 57449510182094815058909537)
  ·
    refine ⟨43087132636571111294182153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57449510182094815058909537 43087132636571111294182153)
    ·
      refine ⟨32315349477428333470636615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43087132636571111294182153 32315349477428333470636615)
      ·
        refine ⟨48473024216142500205954923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32315349477428333470636615 48473024216142500205954923)
        ·
          refine ⟨72709536324213750308932385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48473024216142500205954923 72709536324213750308932385)
          ·
            refine ⟨54532152243160312731699289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72709536324213750308932385 54532152243160312731699289)
            ·
              refine ⟨40899114182370234548774467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54532152243160312731699289 40899114182370234548774467)
              ·
                refine ⟨61348671273555351823161701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40899114182370234548774467 61348671273555351823161701)
                ·
                  refine ⟨11502875863791628466842819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61348671273555351823161701 11502875863791628466842819)
                  ·
                    refine ⟨17254313795687442700264229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11502875863791628466842819 17254313795687442700264229)
                    ·
                      refine ⟨3235183836691395506299543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17254313795687442700264229 3235183836691395506299543)
                      ·
                        rfl

theorem cell23_6300498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_6300498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300498 prefixEnd_6300498 := by exact prefixLift 6300498
  have htrace : WordTrace (prefixWord ++ tailWord_6300498) baseStart_6300498 baseEnd_6300498 := by
    simpa [prefixWord, tailWord_6300498, baseEnd_6300498] using wordTrace_append hprefix tailTrace_6300498
  have hstable : (prefixWord ++ tailWord_6300498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300498).length < 2 ^ (prefixWord ++ tailWord_6300498).sum := by decide
  have hdescent : baseEnd_6300498 < baseStart_6300498 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300511 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6]
def baseStart_6300511 : Nat := 118140960795 + 6300511 * 2 ^ 59
def prefixEnd_6300511 : Nat := 4983230072969 + 3 ^ 40 * 6300511 * 2
def baseEnd_6300511 : Nat := 3235190511939903955436983

theorem tailTrace_6300511 : CollatzResearch.WordTrace tailWord_6300511 prefixEnd_6300511 3235190511939903955436983 := by
  unfold tailWord_6300511
  simp only [CollatzResearch.WordTrace]
  refine ⟨229798514877332163455861387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153199009918221442303907591 229798514877332163455861387)
  ·
    refine ⟨344697772315998245183792081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229798514877332163455861387 344697772315998245183792081)
    ·
      refine ⟨258523329236998683887844061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344697772315998245183792081 258523329236998683887844061)
      ·
        refine ⟨96946248463874506457941523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258523329236998683887844061 96946248463874506457941523)
        ·
          refine ⟨145419372695811759686912285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96946248463874506457941523 145419372695811759686912285)
          ·
            refine ⟨54532264760929409882592107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145419372695811759686912285 54532264760929409882592107)
            ·
              refine ⟨81798397141394114823888161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54532264760929409882592107 81798397141394114823888161)
              ·
                refine ⟨61348797856045586117916121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81798397141394114823888161 61348797856045586117916121)
                ·
                  refine ⟨46011598392034189588437091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61348797856045586117916121 46011598392034189588437091)
                  ·
                    refine ⟨69017397588051284382655637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46011598392034189588437091 69017397588051284382655637)
                    ·
                      refine ⟨3235190511939903955436983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69017397588051284382655637 3235190511939903955436983)
                      ·
                        rfl

theorem cell23_6300511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_6300511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300511 prefixEnd_6300511 := by exact prefixLift 6300511
  have htrace : WordTrace (prefixWord ++ tailWord_6300511) baseStart_6300511 baseEnd_6300511 := by
    simpa [prefixWord, tailWord_6300511, baseEnd_6300511] using wordTrace_append hprefix tailTrace_6300511
  have hstable : (prefixWord ++ tailWord_6300511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300511).length < 2 ^ (prefixWord ++ tailWord_6300511).sum := by decide
  have hdescent : baseEnd_6300511 < baseStart_6300511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300515 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 2, 4, 2]
def baseStart_6300515 : Nat := 118140960795 + 6300515 * 2 ^ 59
def prefixEnd_6300515 : Nat := 4983230072969 + 3 ^ 40 * 6300515 * 2
def baseEnd_6300515 : Nat := 3235192565862521939786965

theorem tailTrace_6300515 : CollatzResearch.WordTrace tailWord_6300515 prefixEnd_6300515 3235192565862521939786965 := by
  unfold tailWord_6300515
  simp only [CollatzResearch.WordTrace]
  refine ⟨229798660769317672139006999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153199107179545114759337999 229798660769317672139006999)
  ·
    refine ⟨344697991153976508208510499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229798660769317672139006999 344697991153976508208510499)
    ·
      refine ⟨517046986730964762312765749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344697991153976508208510499 517046986730964762312765749)
      ·
        refine ⟨48473155006027946466821789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 517046986730964762312765749 48473155006027946466821789)
        ·
          refine ⟨18177433127260479925058171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48473155006027946466821789 18177433127260479925058171)
          ·
            refine ⟨27266149690890719887587257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18177433127260479925058171 27266149690890719887587257)
            ·
              refine ⟨20449612268168039915690443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27266149690890719887587257 20449612268168039915690443)
              ·
                refine ⟨30674418402252059873535665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20449612268168039915690443 30674418402252059873535665)
                ·
                  refine ⟨23005813801689044905151749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30674418402252059873535665 23005813801689044905151749)
                  ·
                    refine ⟨4313590087816695919715953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23005813801689044905151749 4313590087816695919715953)
                    ·
                      refine ⟨3235192565862521939786965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313590087816695919715953 3235192565862521939786965)
                      ·
                        rfl

theorem cell23_6300515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_6300515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300515 prefixEnd_6300515 := by exact prefixLift 6300515
  have htrace : WordTrace (prefixWord ++ tailWord_6300515) baseStart_6300515 baseEnd_6300515 := by
    simpa [prefixWord, tailWord_6300515, baseEnd_6300515] using wordTrace_append hprefix tailTrace_6300515
  have hstable : (prefixWord ++ tailWord_6300515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300515).length < 2 ^ (prefixWord ++ tailWord_6300515).sum := by decide
  have hdescent : baseEnd_6300515 < baseStart_6300515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300561 : List Nat := [1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_6300561 : Nat := 118140960795 + 6300561 * 2 ^ 59
def prefixEnd_6300561 : Nat := 4983230072969 + 3 ^ 40 * 6300561 * 2
def baseEnd_6300561 : Nat := 3235216185972628759811753

theorem tailTrace_6300561 : CollatzResearch.WordTrace tailWord_6300561 prefixEnd_6300561 3235216185972628759811753 := by
  unfold tailWord_6300561
  simp only [CollatzResearch.WordTrace]
  refine ⟨229800338527151021995181537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153200225684767347996787691 229800338527151021995181537)
  ·
    refine ⟨172350253895363266496386153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229800338527151021995181537 172350253895363266496386153)
    ·
      refine ⟨129262690421522449872289615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172350253895363266496386153 129262690421522449872289615)
      ·
        refine ⟨193894035632283674808434423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129262690421522449872289615 193894035632283674808434423)
        ·
          refine ⟨290841053448425512212651635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193894035632283674808434423 290841053448425512212651635)
          ·
            refine ⟨436261580172638268318977453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290841053448425512212651635 436261580172638268318977453)
            ·
              refine ⟨163598092564739350619616545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436261580172638268318977453 163598092564739350619616545)
              ·
                refine ⟨122698569423554512964712409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163598092564739350619616545 122698569423554512964712409)
                ·
                  refine ⟨92023927067665884723534307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122698569423554512964712409 92023927067665884723534307)
                  ·
                    refine ⟨138035890601498827085301461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 92023927067665884723534307 138035890601498827085301461)
                    ·
                      refine ⟨3235216185972628759811753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138035890601498827085301461 3235216185972628759811753)
                      ·
                        rfl

theorem cell23_6300561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_6300561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300561 prefixEnd_6300561 := by exact prefixLift 6300561
  have htrace : WordTrace (prefixWord ++ tailWord_6300561) baseStart_6300561 baseEnd_6300561 := by
    simpa [prefixWord, tailWord_6300561, baseEnd_6300561] using wordTrace_append hprefix tailTrace_6300561
  have hstable : (prefixWord ++ tailWord_6300561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300561).length < 2 ^ (prefixWord ++ tailWord_6300561).sum := by decide
  have hdescent : baseEnd_6300561 < baseStart_6300561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300588 : List Nat := [2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 4]
def baseStart_6300588 : Nat := 118140960795 + 6300588 * 2 ^ 59
def prefixEnd_6300588 : Nat := 4983230072969 + 3 ^ 40 * 6300588 * 2
def baseEnd_6300588 : Nat := 3235230049950300154174129

theorem tailTrace_6300588 : CollatzResearch.WordTrace tailWord_6300588 prefixEnd_6300588 3235230049950300154174129 := by
  unfold tailWord_6300588
  simp only [CollatzResearch.WordTrace]
  refine ⟨114900661649026602803207209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153200882198702137070942945 114900661649026602803207209)
  ·
    refine ⟨86175496236769952102405407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114900661649026602803207209 86175496236769952102405407)
    ·
      refine ⟨129263244355154928153608111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86175496236769952102405407 129263244355154928153608111)
      ·
        refine ⟨193894866532732392230412167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129263244355154928153608111 193894866532732392230412167)
        ·
          refine ⟨290842299799098588345618251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193894866532732392230412167 290842299799098588345618251)
          ·
            refine ⟨436263449698647882518427377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290842299799098588345618251 436263449698647882518427377)
            ·
              refine ⟨327197587273985911888820533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436263449698647882518427377 327197587273985911888820533)
              ·
                refine ⟨30674773806936179239576925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327197587273985911888820533 30674773806936179239576925)
                ·
                  refine ⟨11503040177601067214841347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30674773806936179239576925 11503040177601067214841347)
                  ·
                    refine ⟨17254560266401600822262021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11503040177601067214841347 17254560266401600822262021)
                    ·
                      refine ⟨3235230049950300154174129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17254560266401600822262021 3235230049950300154174129)
                      ·
                        rfl

theorem cell23_6300588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 4].length) (baseStart_6300588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300588 prefixEnd_6300588 := by exact prefixLift 6300588
  have htrace : WordTrace (prefixWord ++ tailWord_6300588) baseStart_6300588 baseEnd_6300588 := by
    simpa [prefixWord, tailWord_6300588, baseEnd_6300588] using wordTrace_append hprefix tailTrace_6300588
  have hstable : (prefixWord ++ tailWord_6300588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300588).length < 2 ^ (prefixWord ++ tailWord_6300588).sum := by decide
  have hdescent : baseEnd_6300588 < baseStart_6300588 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300615 : List Nat := [1, 1, 4, 1, 1, 2, 3, 4, 2, 4]
def baseStart_6300615 : Nat := 118140960795 + 6300615 * 2 ^ 59
def prefixEnd_6300615 : Nat := 4983230072969 + 3 ^ 40 * 6300615 * 2
def baseEnd_6300615 : Nat := 1078414637975990516178835

theorem tailTrace_6300615 : CollatzResearch.WordTrace tailWord_6300615 prefixEnd_6300615 1078414637975990516178835 := by
  unfold tailWord_6300615
  simp only [CollatzResearch.WordTrace]
  refine ⟨229802308068955389217647299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153201538712636926145098199 229802308068955389217647299)
  ·
    refine ⟨344703462103433083826470949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229802308068955389217647299 344703462103433083826470949)
    ·
      refine ⟨64631899144393703217463303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344703462103433083826470949 64631899144393703217463303)
      ·
        refine ⟨96947848716590554826194955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64631899144393703217463303 96947848716590554826194955)
        ·
          refine ⟨145421773074885832239292433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96947848716590554826194955 145421773074885832239292433)
          ·
            refine ⟨109066329806164374179469325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145421773074885832239292433 109066329806164374179469325)
            ·
              refine ⟨40899873677311640317300997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109066329806164374179469325 40899873677311640317300997)
              ·
                refine ⟨7668726314495932559493937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40899873677311640317300997 7668726314495932559493937)
                ·
                  refine ⟨5751544735871949419620453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668726314495932559493937 5751544735871949419620453)
                  ·
                    refine ⟨1078414637975990516178835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751544735871949419620453 1078414637975990516178835)
                    ·
                      rfl

theorem cell23_6300615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 4, 2, 4].length) (baseStart_6300615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300615 prefixEnd_6300615 := by exact prefixLift 6300615
  have htrace : WordTrace (prefixWord ++ tailWord_6300615) baseStart_6300615 baseEnd_6300615 := by
    simpa [prefixWord, tailWord_6300615, baseEnd_6300615] using wordTrace_append hprefix tailTrace_6300615
  have hstable : (prefixWord ++ tailWord_6300615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300615).length < 2 ^ (prefixWord ++ tailWord_6300615).sum := by decide
  have hdescent : baseEnd_6300615 < baseStart_6300615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300618 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4]
def baseStart_6300618 : Nat := 118140960795 + 6300618 * 2 ^ 59
def prefixEnd_6300618 : Nat := 4983230072969 + 3 ^ 40 * 6300618 * 2
def baseEnd_6300618 : Nat := 3235245454369935036798991

theorem tailTrace_6300618 : CollatzResearch.WordTrace tailWord_6300618 prefixEnd_6300618 3235245454369935036798991 := by
  unfold tailWord_6300618
  simp only [CollatzResearch.WordTrace]
  refine ⟨57450604371986130182501627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153201611658629680486671005 57450604371986130182501627)
  ·
    refine ⟨86175906557979195273752441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57450604371986130182501627 86175906557979195273752441)
    ·
      refine ⟨64631929918484396455314331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86175906557979195273752441 64631929918484396455314331)
      ·
        refine ⟨96947894877726594682971497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64631929918484396455314331 96947894877726594682971497)
        ·
          refine ⟨72710921158294946012228623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96947894877726594682971497 72710921158294946012228623)
          ·
            refine ⟨109066381737442419018342935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72710921158294946012228623 109066381737442419018342935)
            ·
              refine ⟨163599572606163628527514403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109066381737442419018342935 163599572606163628527514403)
              ·
                refine ⟨245399358909245442791271605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163599572606163628527514403 245399358909245442791271605)
                ·
                  refine ⟨23006189897741760261681713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 245399358909245442791271605 23006189897741760261681713)
                  ·
                    refine ⟨17254642423306320196261285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23006189897741760261681713 17254642423306320196261285)
                    ·
                      refine ⟨3235245454369935036798991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17254642423306320196261285 3235245454369935036798991)
                      ·
                        rfl

theorem cell23_6300618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 5, 2, 4].length) (baseStart_6300618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300618 prefixEnd_6300618 := by exact prefixLift 6300618
  have htrace : WordTrace (prefixWord ++ tailWord_6300618) baseStart_6300618 baseEnd_6300618 := by
    simpa [prefixWord, tailWord_6300618, baseEnd_6300618] using wordTrace_append hprefix tailTrace_6300618
  have hstable : (prefixWord ++ tailWord_6300618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300618).length < 2 ^ (prefixWord ++ tailWord_6300618).sum := by decide
  have hdescent : baseEnd_6300618 < baseStart_6300618 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300639 : List Nat := [1, 1, 2, 3, 5, 1, 1, 2, 3, 2, 2]
def baseStart_6300639 : Nat := 118140960795 + 6300639 * 2 ^ 59
def prefixEnd_6300639 : Nat := 4983230072969 + 3 ^ 40 * 6300639 * 2
def baseEnd_6300639 : Nat := 3235256237463679454636395

theorem tailTrace_6300639 : CollatzResearch.WordTrace tailWord_6300639 prefixEnd_6300639 3235256237463679454636395 := by
  unfold tailWord_6300639
  simp only [CollatzResearch.WordTrace]
  refine ⟨229803183420868441316520971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153202122280578960877680647 229803183420868441316520971)
  ·
    refine ⟨344704775131302661974781457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229803183420868441316520971 344704775131302661974781457)
    ·
      refine ⟨258528581348476996481086093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344704775131302661974781457 258528581348476996481086093)
      ·
        refine ⟨96948218005678873680407285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258528581348476996481086093 96948218005678873680407285)
        ·
          refine ⟨9088895438032394407538183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 96948218005678873680407285 9088895438032394407538183)
          ·
            refine ⟨13633343157048591611307275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9088895438032394407538183 13633343157048591611307275)
            ·
              refine ⟨20450014735572887416960913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13633343157048591611307275 20450014735572887416960913)
              ·
                refine ⟨15337511051679665562720685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20450014735572887416960913 15337511051679665562720685)
                ·
                  refine ⟨5751566644379874586020257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15337511051679665562720685 5751566644379874586020257)
                  ·
                    refine ⟨4313674983284905939515193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751566644379874586020257 4313674983284905939515193)
                    ·
                      refine ⟨3235256237463679454636395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313674983284905939515193 3235256237463679454636395)
                      ·
                        rfl

theorem cell23_6300639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_6300639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300639 prefixEnd_6300639 := by exact prefixLift 6300639
  have htrace : WordTrace (prefixWord ++ tailWord_6300639) baseStart_6300639 baseEnd_6300639 := by
    simpa [prefixWord, tailWord_6300639, baseEnd_6300639] using wordTrace_append hprefix tailTrace_6300639
  have hstable : (prefixWord ++ tailWord_6300639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300639).length < 2 ^ (prefixWord ++ tailWord_6300639).sum := by decide
  have hdescent : baseEnd_6300639 < baseStart_6300639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300655 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3]
def baseStart_6300655 : Nat := 118140960795 + 6300655 * 2 ^ 59
def prefixEnd_6300655 : Nat := 4983230072969 + 3 ^ 40 * 6300655 * 2
def baseEnd_6300655 : Nat := 3235264453154151392036321

theorem tailTrace_6300655 : CollatzResearch.WordTrace tailWord_6300655 prefixEnd_6300655 3235264453154151392036321 := by
  unfold tailWord_6300655
  simp only [CollatzResearch.WordTrace]
  refine ⟨229803766988810476049103419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153202511325873650699402279 229803766988810476049103419)
  ·
    refine ⟨344705650483215714073655129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229803766988810476049103419 344705650483215714073655129)
    ·
      refine ⟨258529237862411785555241347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344705650483215714073655129 258529237862411785555241347)
      ·
        refine ⟨387793856793617678332862021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258529237862411785555241347 387793856793617678332862021)
        ·
          refine ⟨72711348148803314687411629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 387793856793617678332862021 72711348148803314687411629)
          ·
            refine ⟨27266755555801243007779361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72711348148803314687411629 27266755555801243007779361)
            ·
              refine ⟨20450066666850932255834521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27266755555801243007779361 20450066666850932255834521)
              ·
                refine ⟨15337550000138199191875891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20450066666850932255834521 15337550000138199191875891)
                ·
                  refine ⟨23006325000207298787813837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15337550000138199191875891 23006325000207298787813837)
                  ·
                    refine ⟨8627371875077737045430189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23006325000207298787813837 8627371875077737045430189)
                    ·
                      refine ⟨3235264453154151392036321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8627371875077737045430189 3235264453154151392036321)
                      ·
                        rfl

theorem cell23_6300655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 3, 3].length) (baseStart_6300655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300655 prefixEnd_6300655 := by exact prefixLift 6300655
  have htrace : WordTrace (prefixWord ++ tailWord_6300655) baseStart_6300655 baseEnd_6300655 := by
    simpa [prefixWord, tailWord_6300655, baseEnd_6300655] using wordTrace_append hprefix tailTrace_6300655
  have hstable : (prefixWord ++ tailWord_6300655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300655).length < 2 ^ (prefixWord ++ tailWord_6300655).sum := by decide
  have hdescent : baseEnd_6300655 < baseStart_6300655 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300729 : List Nat := [1, 2, 1, 5, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6300729 : Nat := 118140960795 + 6300729 * 2 ^ 59
def prefixEnd_6300729 : Nat := 4983230072969 + 3 ^ 40 * 6300729 * 2
def baseEnd_6300729 : Nat := 3235302450722584102510981

theorem tailTrace_6300729 : CollatzResearch.WordTrace tailWord_6300729 prefixEnd_6300729 3235302450722584102510981 := by
  unfold tailWord_6300729
  simp only [CollatzResearch.WordTrace]
  refine ⟨229806465990542386687297241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153204310660361591124864827 229806465990542386687297241)
  ·
    refine ⟨172354849492906790015472931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229806465990542386687297241 172354849492906790015472931)
    ·
      refine ⟨258532274239360185023209397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172354849492906790015472931 258532274239360185023209397)
      ·
        refine ⟨24237400709940017345925881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258532274239360185023209397 24237400709940017345925881)
        ·
          refine ⟨18178050532455013009444411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24237400709940017345925881 18178050532455013009444411)
          ·
            refine ⟨27267075798682519514166617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18178050532455013009444411 27267075798682519514166617)
            ·
              refine ⟨20450306849011889635624963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27267075798682519514166617 20450306849011889635624963)
              ·
                refine ⟨30675460273517834453437445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20450306849011889635624963 30675460273517834453437445)
                ·
                  refine ⟨5751648801284593960019521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30675460273517834453437445 5751648801284593960019521)
                  ·
                    refine ⟨4313736600963445470014641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751648801284593960019521 4313736600963445470014641)
                    ·
                      refine ⟨3235302450722584102510981, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313736600963445470014641 3235302450722584102510981)
                      ·
                        rfl

theorem cell23_6300729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6300729 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300729 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300729 prefixEnd_6300729 := by exact prefixLift 6300729
  have htrace : WordTrace (prefixWord ++ tailWord_6300729) baseStart_6300729 baseEnd_6300729 := by
    simpa [prefixWord, tailWord_6300729, baseEnd_6300729] using wordTrace_append hprefix tailTrace_6300729
  have hstable : (prefixWord ++ tailWord_6300729).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300729).length < 2 ^ (prefixWord ++ tailWord_6300729).sum := by decide
  have hdescent : baseEnd_6300729 < baseStart_6300729 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300746 : List Nat := [3, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2]
def baseStart_6300746 : Nat := 118140960795 + 6300746 * 2 ^ 59
def prefixEnd_6300746 : Nat := 4983230072969 + 3 ^ 40 * 6300746 * 2
def baseEnd_6300746 : Nat := 3235311179893710535998403

theorem tailTrace_6300746 : CollatzResearch.WordTrace tailWord_6300746 prefixEnd_6300746 3235311179893710535998403 := by
  unfold tailWord_6300746
  simp only [CollatzResearch.WordTrace]
  refine ⟨57451771507870199647666523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153204724020987199060444061 57451771507870199647666523)
  ·
    refine ⟨86177657261805299471499785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57451771507870199647666523 86177657261805299471499785)
    ·
      refine ⟨64633242946353974603624839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86177657261805299471499785 64633242946353974603624839)
      ·
        refine ⟨96949864419530961905437259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64633242946353974603624839 96949864419530961905437259)
        ·
          refine ⟨145424796629296442858155889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96949864419530961905437259 145424796629296442858155889)
          ·
            refine ⟨109068597471972332143616917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145424796629296442858155889 109068597471972332143616917)
            ·
              refine ⟨5112590506498703069232043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109068597471972332143616917 5112590506498703069232043)
              ·
                refine ⟨7668885759748054603848065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112590506498703069232043 7668885759748054603848065)
                ·
                  refine ⟨5751664319811040952886049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7668885759748054603848065 5751664319811040952886049)
                  ·
                    refine ⟨4313748239858280714664537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751664319811040952886049 4313748239858280714664537)
                    ·
                      refine ⟨3235311179893710535998403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313748239858280714664537 3235311179893710535998403)
                      ·
                        rfl

theorem cell23_6300746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 6, 1, 2, 2, 2].length) (baseStart_6300746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300746 prefixEnd_6300746 := by exact prefixLift 6300746
  have htrace : WordTrace (prefixWord ++ tailWord_6300746) baseStart_6300746 baseEnd_6300746 := by
    simpa [prefixWord, tailWord_6300746, baseEnd_6300746] using wordTrace_append hprefix tailTrace_6300746
  have hstable : (prefixWord ++ tailWord_6300746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300746).length < 2 ^ (prefixWord ++ tailWord_6300746).sum := by decide
  have hdescent : baseEnd_6300746 < baseStart_6300746 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300775 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5]
def baseStart_6300775 : Nat := 118140960795 + 6300775 * 2 ^ 59
def prefixEnd_6300775 : Nat := 4983230072969 + 3 ^ 40 * 6300775 * 2
def baseEnd_6300775 : Nat := 3235326070832690922535769

theorem tailTrace_6300775 : CollatzResearch.WordTrace tailWord_6300775 prefixEnd_6300775 3235326070832690922535769 := by
  unfold tailWord_6300775
  simp only [CollatzResearch.WordTrace]
  refine ⟨229808143748375736543471779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153205429165583824362314519 229808143748375736543471779)
  ·
    refine ⟨344712215622563604815207669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229808143748375736543471779 344712215622563604815207669)
    ·
      refine ⟨32316770214615337951425719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 344712215622563604815207669 32316770214615337951425719)
      ·
        refine ⟨48475155321923006927138579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32316770214615337951425719 48475155321923006927138579)
        ·
          refine ⟨72712732982884510390707869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48475155321923006927138579 72712732982884510390707869)
          ·
            refine ⟨27267274868581691396515451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72712732982884510390707869 27267274868581691396515451)
            ·
              refine ⟨40900912302872537094773177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27267274868581691396515451 40900912302872537094773177)
              ·
                refine ⟨30675684227154402821079883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40900912302872537094773177 30675684227154402821079883)
                ·
                  refine ⟨46013526340731604231619825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30675684227154402821079883 46013526340731604231619825)
                  ·
                    refine ⟨34510144755548703173714869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46013526340731604231619825 34510144755548703173714869)
                    ·
                      refine ⟨3235326070832690922535769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34510144755548703173714869 3235326070832690922535769)
                      ·
                        rfl

theorem cell23_6300775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 2, 5].length) (baseStart_6300775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300775 prefixEnd_6300775 := by exact prefixLift 6300775
  have htrace : WordTrace (prefixWord ++ tailWord_6300775) baseStart_6300775 baseEnd_6300775 := by
    simpa [prefixWord, tailWord_6300775, baseEnd_6300775] using wordTrace_append hprefix tailTrace_6300775
  have hstable : (prefixWord ++ tailWord_6300775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300775).length < 2 ^ (prefixWord ++ tailWord_6300775).sum := by decide
  have hdescent : baseEnd_6300775 < baseStart_6300775 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300782 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 2, 5]
def baseStart_6300782 : Nat := 118140960795 + 6300782 * 2 ^ 59
def prefixEnd_6300782 : Nat := 4983230072969 + 3 ^ 40 * 6300782 * 2
def baseEnd_6300782 : Nat := 1078443221732424131716079

theorem tailTrace_6300782 : CollatzResearch.WordTrace tailWord_6300782 prefixEnd_6300782 1078443221732424131716079 := by
  unfold tailWord_6300782
  simp only [CollatzResearch.WordTrace]
  refine ⟨28726049882418797092372075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153205599372900251159317733 28726049882418797092372075)
  ·
    refine ⟨43089074823628195638558113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28726049882418797092372075 43089074823628195638558113)
    ·
      refine ⟨32316806117721146728918585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43089074823628195638558113 32316806117721146728918585)
      ·
        refine ⟨24237604588290860046688939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32316806117721146728918585 24237604588290860046688939)
        ·
          refine ⟨36356406882436290070033409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24237604588290860046688939 36356406882436290070033409)
          ·
            refine ⟨27267305161827217552525057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36356406882436290070033409 27267305161827217552525057)
            ·
              refine ⟨20450478871370413164393793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27267305161827217552525057 20450478871370413164393793)
              ·
                refine ⟨15337859153527809873295345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20450478871370413164393793 15337859153527809873295345)
                ·
                  refine ⟨11503394365145857404971509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15337859153527809873295345 11503394365145857404971509)
                  ·
                    refine ⟨1078443221732424131716079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11503394365145857404971509 1078443221732424131716079)
                    ·
                      rfl

theorem cell23_6300782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 2, 5].length) (baseStart_6300782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300782 prefixEnd_6300782 := by exact prefixLift 6300782
  have htrace : WordTrace (prefixWord ++ tailWord_6300782) baseStart_6300782 baseEnd_6300782 := by
    simpa [prefixWord, tailWord_6300782, baseEnd_6300782] using wordTrace_append hprefix tailTrace_6300782
  have hstable : (prefixWord ++ tailWord_6300782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300782).length < 2 ^ (prefixWord ++ tailWord_6300782).sum := by decide
  have hdescent : baseEnd_6300782 < baseStart_6300782 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300785 : List Nat := [1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_6300785 : Nat := 118140960795 + 6300785 * 2 ^ 59
def prefixEnd_6300785 : Nat := 4983230072969 + 3 ^ 40 * 6300785 * 2
def baseEnd_6300785 : Nat := 3235331205639235883410723

theorem tailTrace_6300785 : CollatzResearch.WordTrace tailWord_6300785 prefixEnd_6300785 3235331205639235883410723 := by
  unfold tailWord_6300785
  simp only [CollatzResearch.WordTrace]
  refine ⟨229808508478339508251335809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153205672318893005500890539 229808508478339508251335809)
  ·
    refine ⟨172356381358754631188501857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229808508478339508251335809 172356381358754631188501857)
    ·
      refine ⟨129267286019065973391376393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172356381358754631188501857 129267286019065973391376393)
      ·
        refine ⟨96950464514299480043532295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129267286019065973391376393 96950464514299480043532295)
        ·
          refine ⟨145425696771449220065298443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96950464514299480043532295 145425696771449220065298443)
          ·
            refine ⟨218138545157173830097947665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145425696771449220065298443 218138545157173830097947665)
            ·
              refine ⟨163603908867880372573460749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218138545157173830097947665 163603908867880372573460749)
              ·
                refine ⟨61351465825455139715047781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163603908867880372573460749 61351465825455139715047781)
                ·
                  refine ⟨11503399842272838696571459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61351465825455139715047781 11503399842272838696571459)
                  ·
                    refine ⟨17255099763409258044857189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11503399842272838696571459 17255099763409258044857189)
                    ·
                      refine ⟨3235331205639235883410723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17255099763409258044857189 3235331205639235883410723)
                      ·
                        rfl

theorem cell23_6300785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_6300785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300785 prefixEnd_6300785 := by exact prefixLift 6300785
  have htrace : WordTrace (prefixWord ++ tailWord_6300785) baseStart_6300785 baseEnd_6300785 := by
    simpa [prefixWord, tailWord_6300785, baseEnd_6300785] using wordTrace_append hprefix tailTrace_6300785
  have hstable : (prefixWord ++ tailWord_6300785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300785).length < 2 ^ (prefixWord ++ tailWord_6300785).sum := by decide
  have hdescent : baseEnd_6300785 < baseStart_6300785 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300795 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 7, 4]
def baseStart_6300795 : Nat := 118140960795 + 6300795 * 2 ^ 59
def prefixEnd_6300795 : Nat := 4983230072969 + 3 ^ 40 * 6300795 * 2
def baseEnd_6300795 : Nat := 1078445446815260281428559

theorem tailTrace_6300795 : CollatzResearch.WordTrace tailWord_6300795 prefixEnd_6300795 1078445446815260281428559 := by
  unfold tailWord_6300795
  simp only [CollatzResearch.WordTrace]
  refine ⟨229808873208303279959199839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153205915472202186639466559 229808873208303279959199839)
  ·
    refine ⟨344713309812454919938799759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229808873208303279959199839 344713309812454919938799759)
    ·
      refine ⟨517069964718682379908199639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344713309812454919938799759 517069964718682379908199639)
      ·
        refine ⟨775604947078023569862299459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517069964718682379908199639 775604947078023569862299459)
        ·
          refine ⟨1163407420617035354793449189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775604947078023569862299459 1163407420617035354793449189)
          ·
            refine ⟨218138891365694129023771723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1163407420617035354793449189 218138891365694129023771723)
            ·
              refine ⟨327208337048541193535657585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218138891365694129023771723 327208337048541193535657585)
              ·
                refine ⟨245406252786405895151743189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327208337048541193535657585 245406252786405895151743189)
                ·
                  refine ⟨5751709049681388167618981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 245406252786405895151743189 5751709049681388167618981)
                  ·
                    refine ⟨1078445446815260281428559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5751709049681388167618981 1078445446815260281428559)
                    ·
                      rfl

theorem cell23_6300795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 7, 4].length) (baseStart_6300795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300795 prefixEnd_6300795 := by exact prefixLift 6300795
  have htrace : WordTrace (prefixWord ++ tailWord_6300795) baseStart_6300795 baseEnd_6300795 := by
    simpa [prefixWord, tailWord_6300795, baseEnd_6300795] using wordTrace_append hprefix tailTrace_6300795
  have hstable : (prefixWord ++ tailWord_6300795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300795).length < 2 ^ (prefixWord ++ tailWord_6300795).sum := by decide
  have hdescent : baseEnd_6300795 < baseStart_6300795 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300835 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3]
def baseStart_6300835 : Nat := 118140960795 + 6300835 * 2 ^ 59
def prefixEnd_6300835 : Nat := 4983230072969 + 3 ^ 40 * 6300835 * 2
def baseEnd_6300835 : Nat := 3235356879671960687785493

theorem tailTrace_6300835 : CollatzResearch.WordTrace tailWord_6300835 prefixEnd_6300835 3235356879671960687785493 := by
  unfold tailWord_6300835
  simp only [CollatzResearch.WordTrace]
  refine ⟨229810332128158366790655959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153206888085438911193770639 229810332128158366790655959)
  ·
    refine ⟨344715498192237550185983939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229810332128158366790655959 344715498192237550185983939)
    ·
      refine ⟨517073247288356325278975909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344715498192237550185983939 517073247288356325278975909)
      ·
        refine ⟨96951233866566810989807983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517073247288356325278975909 96951233866566810989807983)
        ·
          refine ⟨145426850799850216484711975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96951233866566810989807983 145426850799850216484711975)
          ·
            refine ⟨218140276199775324727067963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145426850799850216484711975 218140276199775324727067963)
            ·
              refine ⟨327210414299662987090601945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218140276199775324727067963 327210414299662987090601945)
              ·
                refine ⟨245407810724747240317951459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327210414299662987090601945 245407810724747240317951459)
                ·
                  refine ⟨368111716087120860476927189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245407810724747240317951459 368111716087120860476927189)
                  ·
                    refine ⟨8627618345791895167427981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 368111716087120860476927189 8627618345791895167427981)
                    ·
                      refine ⟨3235356879671960687785493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8627618345791895167427981 3235356879671960687785493)
                      ·
                        rfl

theorem cell23_6300835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_6300835 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300835 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300835 prefixEnd_6300835 := by exact prefixLift 6300835
  have htrace : WordTrace (prefixWord ++ tailWord_6300835) baseStart_6300835 baseEnd_6300835 := by
    simpa [prefixWord, tailWord_6300835, baseEnd_6300835] using wordTrace_append hprefix tailTrace_6300835
  have hstable : (prefixWord ++ tailWord_6300835).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300835).length < 2 ^ (prefixWord ++ tailWord_6300835).sum := by decide
  have hdescent : baseEnd_6300835 < baseStart_6300835 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300872 : List Nat := [2, 1, 3, 1, 2, 1, 3, 4, 1, 5]
def baseStart_6300872 : Nat := 118140960795 + 6300872 * 2 ^ 59
def prefixEnd_6300872 : Nat := 4983230072969 + 3 ^ 40 * 6300872 * 2
def baseEnd_6300872 : Nat := 1078458626152059014340941

theorem tailTrace_6300872 : CollatzResearch.WordTrace tailWord_6300872 prefixEnd_6300872 1078458626152059014340941 := by
  unfold tailWord_6300872
  simp only [CollatzResearch.WordTrace]
  refine ⟨114905840814512161054876435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153207787752682881406501913 114905840814512161054876435)
  ·
    refine ⟨172358761221768241582314653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114905840814512161054876435 172358761221768241582314653)
    ·
      refine ⟨64634535458163090593367995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172358761221768241582314653 64634535458163090593367995)
      ·
        refine ⟨96951803187244635890051993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64634535458163090593367995 96951803187244635890051993)
        ·
          refine ⟨72713852390433476917538995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96951803187244635890051993 72713852390433476917538995)
          ·
            refine ⟨109070778585650215376308493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72713852390433476917538995 109070778585650215376308493)
            ·
              refine ⟨40901541969618830766115685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109070778585650215376308493 40901541969618830766115685)
              ·
                refine ⟨7669039119303530768646691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40901541969618830766115685 7669039119303530768646691)
                ·
                  refine ⟨11503558678955296152970037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669039119303530768646691 11503558678955296152970037)
                  ·
                    refine ⟨1078458626152059014340941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11503558678955296152970037 1078458626152059014340941)
                    ·
                      rfl

theorem cell23_6300872_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 4, 1, 5].length) (baseStart_6300872 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300872 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300872 prefixEnd_6300872 := by exact prefixLift 6300872
  have htrace : WordTrace (prefixWord ++ tailWord_6300872) baseStart_6300872 baseEnd_6300872 := by
    simpa [prefixWord, tailWord_6300872, baseEnd_6300872] using wordTrace_append hprefix tailTrace_6300872
  have hstable : (prefixWord ++ tailWord_6300872).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300872).length < 2 ^ (prefixWord ++ tailWord_6300872).sum := by decide
  have hdescent : baseEnd_6300872 < baseStart_6300872 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300872) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300903 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6300903 : Nat := 118140960795 + 6300903 * 2 ^ 59
def prefixEnd_6300903 : Nat := 4983230072969 + 3 ^ 40 * 6300903 * 2
def baseEnd_6300903 : Nat := 3235391796356466421735181

theorem tailTrace_6300903 : CollatzResearch.WordTrace tailWord_6300903 prefixEnd_6300903 3235391796356466421735181 := by
  unfold tailWord_6300903
  simp only [CollatzResearch.WordTrace]
  refine ⟨229812812291912014404131363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153208541527941342936087575 229812812291912014404131363)
  ·
    refine ⟨344719218437868021606197045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229812812291912014404131363 344719218437868021606197045)
    ·
      refine ⟨32317426728550127025580973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 344719218437868021606197045 32317426728550127025580973)
      ·
        refine ⟨12119035023206297634592865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32317426728550127025580973 12119035023206297634592865)
        ·
          refine ⟨9089276267404723225944649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12119035023206297634592865 9089276267404723225944649)
          ·
            refine ⟨6816957200553542419458487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9089276267404723225944649 6816957200553542419458487)
            ·
              refine ⟨10225435800830313629187731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6816957200553542419458487 10225435800830313629187731)
              ·
                refine ⟨15338153701245470443781597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10225435800830313629187731 15338153701245470443781597)
                ·
                  refine ⟨5751807637967051416418099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15338153701245470443781597 5751807637967051416418099)
                  ·
                    refine ⟨8627711456950577124627149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5751807637967051416418099 8627711456950577124627149)
                    ·
                      refine ⟨3235391796356466421735181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8627711456950577124627149 3235391796356466421735181)
                      ·
                        rfl

theorem cell23_6300903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6300903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300903 prefixEnd_6300903 := by exact prefixLift 6300903
  have htrace : WordTrace (prefixWord ++ tailWord_6300903) baseStart_6300903 baseEnd_6300903 := by
    simpa [prefixWord, tailWord_6300903, baseEnd_6300903] using wordTrace_append hprefix tailTrace_6300903
  have hstable : (prefixWord ++ tailWord_6300903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300903).length < 2 ^ (prefixWord ++ tailWord_6300903).sum := by decide
  have hdescent : baseEnd_6300903 < baseStart_6300903 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300905 : List Nat := [1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 4]
def baseStart_6300905 : Nat := 118140960795 + 6300905 * 2 ^ 59
def prefixEnd_6300905 : Nat := 4983230072969 + 3 ^ 40 * 6300905 * 2
def baseEnd_6300905 : Nat := 3235392823317775413910171

theorem tailTrace_6300905 : CollatzResearch.WordTrace tailWord_6300905 prefixEnd_6300905 3235392823317775413910171 := by
  unfold tailWord_6300905
  simp only [CollatzResearch.WordTrace]
  refine ⟨229812885237904768745704169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153208590158603179163802779 229812885237904768745704169)
  ·
    refine ⟨172359663928428576559278127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229812885237904768745704169 172359663928428576559278127)
    ·
      refine ⟨258539495892642864838917191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172359663928428576559278127 258539495892642864838917191)
      ·
        refine ⟨387809243838964297258375787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258539495892642864838917191 387809243838964297258375787)
        ·
          refine ⟨581713865758446445887563681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387809243838964297258375787 581713865758446445887563681)
          ·
            refine ⟨436285399318834834415672761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 581713865758446445887563681 436285399318834834415672761)
            ·
              refine ⟨327214049489126125811754571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436285399318834834415672761 327214049489126125811754571)
              ·
                refine ⟨490821074233689188717631857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327214049489126125811754571 490821074233689188717631857)
                ·
                  refine ⟨368115805675266891538223893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 490821074233689188717631857 368115805675266891538223893)
                  ·
                    refine ⟨17255428391028135540854245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 368115805675266891538223893 17255428391028135540854245)
                    ·
                      refine ⟨3235392823317775413910171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17255428391028135540854245 3235392823317775413910171)
                      ·
                        rfl

theorem cell23_6300905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 1, 2, 6, 4].length) (baseStart_6300905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300905 prefixEnd_6300905 := by exact prefixLift 6300905
  have htrace : WordTrace (prefixWord ++ tailWord_6300905) baseStart_6300905 baseEnd_6300905 := by
    simpa [prefixWord, tailWord_6300905, baseEnd_6300905] using wordTrace_append hprefix tailTrace_6300905
  have hstable : (prefixWord ++ tailWord_6300905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300905).length < 2 ^ (prefixWord ++ tailWord_6300905).sum := by decide
  have hdescent : baseEnd_6300905 < baseStart_6300905 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300915 : List Nat := [1, 1, 1, 2, 2, 5, 1, 10]
def baseStart_6300915 : Nat := 118140960795 + 6300915 * 2 ^ 59
def prefixEnd_6300915 : Nat := 4983230072969 + 3 ^ 40 * 6300915 * 2
def baseEnd_6300915 : Nat := 119829554004604458325375

theorem tailTrace_6300915 : CollatzResearch.WordTrace tailWord_6300915 prefixEnd_6300915 119829554004604458325375 := by
  unfold tailWord_6300915
  simp only [CollatzResearch.WordTrace]
  refine ⟨229813249967868540453568199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153208833311912360302378799 229813249967868540453568199)
  ·
    refine ⟨344719874951802810680352299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229813249967868540453568199 344719874951802810680352299)
    ·
      refine ⟨517079812427704216020528449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344719874951802810680352299 517079812427704216020528449)
      ·
        refine ⟨387809859320778162015396337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517079812427704216020528449 387809859320778162015396337)
        ·
          refine ⟨290857394490583621511547253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387809859320778162015396337 290857394490583621511547253)
          ·
            refine ⟨27267880733492214516707555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 290857394490583621511547253 27267880733492214516707555)
            ·
              refine ⟨40901821100238321775061333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27267880733492214516707555 40901821100238321775061333)
              ·
                refine ⟨119829554004604458325375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 40901821100238321775061333 119829554004604458325375)
                ·
                  rfl

theorem cell23_6300915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 1, 10].length) (baseStart_6300915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300915 prefixEnd_6300915 := by exact prefixLift 6300915
  have htrace : WordTrace (prefixWord ++ tailWord_6300915) baseStart_6300915 baseEnd_6300915 := by
    simpa [prefixWord, tailWord_6300915, baseEnd_6300915] using wordTrace_append hprefix tailTrace_6300915
  have hstable : (prefixWord ++ tailWord_6300915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300915).length < 2 ^ (prefixWord ++ tailWord_6300915).sum := by decide
  have hdescent : baseEnd_6300915 < baseStart_6300915 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300922 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4]
def baseStart_6300922 : Nat := 118140960795 + 6300922 * 2 ^ 59
def prefixEnd_6300922 : Nat := 4983230072969 + 3 ^ 40 * 6300922 * 2
def baseEnd_6300922 : Nat := 3235401552488901847397593

theorem tailTrace_6300922 : CollatzResearch.WordTrace tailWord_6300922 prefixEnd_6300922 3235401552488901847397593 := by
  unfold tailWord_6300922
  simp only [CollatzResearch.WordTrace]
  refine ⟨57453376319710795162268255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153209003519228787099382013 57453376319710795162268255)
  ·
    refine ⟨86180064479566192743402383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57453376319710795162268255 86180064479566192743402383)
    ·
      refine ⟨129270096719349289115103575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86180064479566192743402383 129270096719349289115103575)
      ·
        refine ⟨193905145079023933672655363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129270096719349289115103575 193905145079023933672655363)
        ·
          refine ⟨290857717618535900508983045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193905145079023933672655363 290857717618535900508983045)
          ·
            refine ⟨54535822053475481345434321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290857717618535900508983045 54535822053475481345434321)
            ·
              refine ⟨40901866540106611009075741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54535822053475481345434321 40901866540106611009075741)
              ·
                refine ⟨15338199952539979128403403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40901866540106611009075741 15338199952539979128403403)
                ·
                  refine ⟨23007299928809968692605105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15338199952539979128403403 23007299928809968692605105)
                  ·
                    refine ⟨17255474946607476519453829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23007299928809968692605105 17255474946607476519453829)
                    ·
                      refine ⟨3235401552488901847397593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17255474946607476519453829 3235401552488901847397593)
                      ·
                        rfl

theorem cell23_6300922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 1, 2, 4].length) (baseStart_6300922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300922 prefixEnd_6300922 := by exact prefixLift 6300922
  have htrace : WordTrace (prefixWord ++ tailWord_6300922) baseStart_6300922 baseEnd_6300922 := by
    simpa [prefixWord, tailWord_6300922, baseEnd_6300922] using wordTrace_append hprefix tailTrace_6300922
  have hstable : (prefixWord ++ tailWord_6300922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300922).length < 2 ^ (prefixWord ++ tailWord_6300922).sum := by decide
  have hdescent : baseEnd_6300922 < baseStart_6300922 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300926 : List Nat := [4, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_6300926 : Nat := 118140960795 + 6300926 * 2 ^ 59
def prefixEnd_6300926 : Nat := 4983230072969 + 3 ^ 40 * 6300926 * 2
def baseEnd_6300926 : Nat := 3235403606411519831747575

theorem tailTrace_6300926 : CollatzResearch.WordTrace tailWord_6300926 prefixEnd_6300926 3235403606411519831747575 := by
  unfold tailWord_6300926
  simp only [CollatzResearch.WordTrace]
  refine ⟨28726706396353586166527329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153209100780552459554812421 28726706396353586166527329)
  ·
    refine ⟨21545029797265189624895497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28726706396353586166527329 21545029797265189624895497)
    ·
      refine ⟨16158772347948892218671623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21545029797265189624895497 16158772347948892218671623)
      ·
        refine ⟨24238158521923338328007435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16158772347948892218671623 24238158521923338328007435)
        ·
          refine ⟨36357237782885007492011153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24238158521923338328007435 36357237782885007492011153)
          ·
            refine ⟨27267928337163755619008365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36357237782885007492011153 27267928337163755619008365)
            ·
              refine ⟨10225473126436408357128137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27267928337163755619008365 10225473126436408357128137)
              ·
                refine ⟨7669104844827306267846103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10225473126436408357128137 7669104844827306267846103)
                ·
                  refine ⟨11503657267240959401769155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669104844827306267846103 11503657267240959401769155)
                  ·
                    refine ⟨17255485900861439102653733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11503657267240959401769155 17255485900861439102653733)
                    ·
                      refine ⟨3235403606411519831747575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17255485900861439102653733 3235403606411519831747575)
                      ·
                        rfl

theorem cell23_6300926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_6300926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300926 prefixEnd_6300926 := by exact prefixLift 6300926
  have htrace : WordTrace (prefixWord ++ tailWord_6300926) baseStart_6300926 baseEnd_6300926 := by
    simpa [prefixWord, tailWord_6300926, baseEnd_6300926] using wordTrace_append hprefix tailTrace_6300926
  have hstable : (prefixWord ++ tailWord_6300926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300926).length < 2 ^ (prefixWord ++ tailWord_6300926).sum := by decide
  have hdescent : baseEnd_6300926 < baseStart_6300926 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300929 : List Nat := [1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_6300929 : Nat := 118140960795 + 6300929 * 2 ^ 59
def prefixEnd_6300929 : Nat := 4983230072969 + 3 ^ 40 * 6300929 * 2
def baseEnd_6300929 : Nat := 3235405146853483320010061

theorem tailTrace_6300929 : CollatzResearch.WordTrace tailWord_6300929 prefixEnd_6300929 3235405146853483320010061 := by
  unfold tailWord_6300929
  simp only [CollatzResearch.WordTrace]
  refine ⟨229813760589817820844577841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153209173726545213896385227 229813760589817820844577841)
  ·
    refine ⟨172360320442363365633433381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229813760589817820844577841 172360320442363365633433381)
    ·
      refine ⟨32317560082943131056268759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172360320442363365633433381 32317560082943131056268759)
      ·
        refine ⟨48476340124414696584403139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32317560082943131056268759 48476340124414696584403139)
        ·
          refine ⟨72714510186622044876604709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48476340124414696584403139 72714510186622044876604709)
          ·
            refine ⟨13633970659991633414363383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72714510186622044876604709 13633970659991633414363383)
            ·
              refine ⟨20450955989987450121545075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13633970659991633414363383 20450955989987450121545075)
              ·
                refine ⟨30676433984981175182317613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20450955989987450121545075 30676433984981175182317613)
                ·
                  refine ⟨11503662744367940693369105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30676433984981175182317613 11503662744367940693369105)
                  ·
                    refine ⟨8627747058275955520026829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11503662744367940693369105 8627747058275955520026829)
                    ·
                      refine ⟨3235405146853483320010061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8627747058275955520026829 3235405146853483320010061)
                      ·
                        rfl

theorem cell23_6300929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_6300929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300929 prefixEnd_6300929 := by exact prefixLift 6300929
  have htrace : WordTrace (prefixWord ++ tailWord_6300929) baseStart_6300929 baseEnd_6300929 := by
    simpa [prefixWord, tailWord_6300929, baseEnd_6300929] using wordTrace_append hprefix tailTrace_6300929
  have hstable : (prefixWord ++ tailWord_6300929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300929).length < 2 ^ (prefixWord ++ tailWord_6300929).sum := by decide
  have hdescent : baseEnd_6300929 < baseStart_6300929 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300932 : List Nat := [2, 3, 2, 2, 2, 1, 2, 9]
def baseStart_6300932 : Nat := 118140960795 + 6300932 * 2 ^ 59
def prefixEnd_6300932 : Nat := 4983230072969 + 3 ^ 40 * 6300932 * 2
def baseEnd_6300932 : Nat := 119829877307238770676761

theorem tailTrace_6300932 : CollatzResearch.WordTrace tailWord_6300932 prefixEnd_6300932 119829877307238770676761 := by
  unfold tailWord_6300932
  simp only [CollatzResearch.WordTrace]
  refine ⟨114906935004403476178468525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153209246672537968237958033 114906935004403476178468525)
  ·
    refine ⟨43090100626651303566925697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114906935004403476178468525 43090100626651303566925697)
    ·
      refine ⟨32317575469988477675194273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43090100626651303566925697 32317575469988477675194273)
      ·
        refine ⟨24238181602491358256395705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32317575469988477675194273 24238181602491358256395705)
        ·
          refine ⟨18178636201868518692296779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24238181602491358256395705 18178636201868518692296779)
          ·
            refine ⟨27267954302802778038445169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18178636201868518692296779 27267954302802778038445169)
            ·
              refine ⟨20450965727102083528833877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27267954302802778038445169 20450965727102083528833877)
              ·
                refine ⟨119829877307238770676761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 20450965727102083528833877 119829877307238770676761)
                ·
                  rfl

theorem cell23_6300932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 2, 9].length) (baseStart_6300932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300932 prefixEnd_6300932 := by exact prefixLift 6300932
  have htrace : WordTrace (prefixWord ++ tailWord_6300932) baseStart_6300932 baseEnd_6300932 := by
    simpa [prefixWord, tailWord_6300932, baseEnd_6300932] using wordTrace_append hprefix tailTrace_6300932
  have hstable : (prefixWord ++ tailWord_6300932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300932).length < 2 ^ (prefixWord ++ tailWord_6300932).sum := by decide
  have hdescent : baseEnd_6300932 < baseStart_6300932 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300960 : List Nat := [2, 1, 1, 5, 3, 1, 1, 4, 1, 2, 2]
def baseStart_6300960 : Nat := 118140960795 + 6300960 * 2 ^ 59
def prefixEnd_6300960 : Nat := 4983230072969 + 3 ^ 40 * 6300960 * 2
def baseEnd_6300960 : Nat := 3235421064753772698722419

theorem tailTrace_6300960 : CollatzResearch.WordTrace tailWord_6300960 prefixEnd_6300960 3235421064753772698722419 := by
  unfold tailWord_6300960
  simp only [CollatzResearch.WordTrace]
  refine ⟨114907445626352756569478167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153209927501803675425970889 114907445626352756569478167)
  ·
    refine ⟨172361168439529134854217251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114907445626352756569478167 172361168439529134854217251)
    ·
      refine ⟨258541752659293702281325877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172361168439529134854217251 258541752659293702281325877)
      ·
        refine ⟨24238289311808784588874301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258541752659293702281325877 24238289311808784588874301)
        ·
          refine ⟨9089358491928294220827863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24238289311808784588874301 9089358491928294220827863)
          ·
            refine ⟨13634037737892441331241795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9089358491928294220827863 13634037737892441331241795)
            ·
              refine ⟨20451056606838661996862693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13634037737892441331241795 20451056606838661996862693)
              ·
                refine ⟨3834573113782249124411755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20451056606838661996862693 3834573113782249124411755)
                ·
                  refine ⟨5751859670673373686617633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834573113782249124411755 5751859670673373686617633)
                  ·
                    refine ⟨4313894753005030264963225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751859670673373686617633 4313894753005030264963225)
                    ·
                      refine ⟨3235421064753772698722419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313894753005030264963225 3235421064753772698722419)
                      ·
                        rfl

theorem cell23_6300960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_6300960 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300960 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300960 prefixEnd_6300960 := by exact prefixLift 6300960
  have htrace : WordTrace (prefixWord ++ tailWord_6300960) baseStart_6300960 baseEnd_6300960 := by
    simpa [prefixWord, tailWord_6300960, baseEnd_6300960] using wordTrace_append hprefix tailTrace_6300960
  have hstable : (prefixWord ++ tailWord_6300960).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300960).length < 2 ^ (prefixWord ++ tailWord_6300960).sum := by decide
  have hdescent : baseEnd_6300960 < baseStart_6300960 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6300986 : List Nat := [3, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2]
def baseStart_6300986 : Nat := 118140960795 + 6300986 * 2 ^ 59
def prefixEnd_6300986 : Nat := 4983230072969 + 3 ^ 40 * 6300986 * 2
def baseEnd_6300986 : Nat := 3235434415250789596997299

theorem tailTrace_6300986 : CollatzResearch.WordTrace tailWord_6300986 prefixEnd_6300986 3235434415250789596997299 := by
  unfold tailWord_6300986
  simp only [CollatzResearch.WordTrace]
  refine ⟨57453959887652829894850703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153210559700407546386268541 57453959887652829894850703)
  ·
    refine ⟨86180939831479244842276055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57453959887652829894850703 86180939831479244842276055)
    ·
      refine ⟨129271409747218867263414083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86180939831479244842276055 129271409747218867263414083)
      ·
        refine ⟨193907114620828300895121125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129271409747218867263414083 193907114620828300895121125)
        ·
          refine ⟨36357583991405306417835211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193907114620828300895121125 36357583991405306417835211)
          ·
            refine ⟨54536375987107959626752817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36357583991405306417835211 54536375987107959626752817)
            ·
              refine ⟨40902281990330969720064613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54536375987107959626752817 40902281990330969720064613)
              ·
                refine ⟨7669177873187056822512115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40902281990330969720064613 7669177873187056822512115)
                ·
                  refine ⟨11503766809780585233768173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669177873187056822512115 11503766809780585233768173)
                  ·
                    refine ⟨4313912553667719462663065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11503766809780585233768173 4313912553667719462663065)
                    ·
                      refine ⟨3235434415250789596997299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313912553667719462663065 3235434415250789596997299)
                      ·
                        rfl

theorem cell23_6300986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 4, 1, 3, 2].length) (baseStart_6300986 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6300986 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6300986 prefixEnd_6300986 := by exact prefixLift 6300986
  have htrace : WordTrace (prefixWord ++ tailWord_6300986) baseStart_6300986 baseEnd_6300986 := by
    simpa [prefixWord, tailWord_6300986, baseEnd_6300986] using wordTrace_append hprefix tailTrace_6300986
  have hstable : (prefixWord ++ tailWord_6300986).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6300986).length < 2 ^ (prefixWord ++ tailWord_6300986).sum := by decide
  have hdescent : baseEnd_6300986 < baseStart_6300986 := by decide
  rcases family_descends (prefixWord ++ tailWord_6300986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301002 : List Nat := [3, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5]
def baseStart_6301002 : Nat := 118140960795 + 6301002 * 2 ^ 59
def prefixEnd_6301002 : Nat := 4983230072969 + 3 ^ 40 * 6301002 * 2
def baseEnd_6301002 : Nat := 3235442630941261534397225

theorem tailTrace_6301002 : CollatzResearch.WordTrace tailWord_6301002 prefixEnd_6301002 3235442630941261534397225 := by
  unfold tailWord_6301002
  simp only [CollatzResearch.WordTrace]
  refine ⟨57454105779638338577996315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153210948745702236207990173 57454105779638338577996315)
  ·
    refine ⟨86181158669457507866994473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57454105779638338577996315 86181158669457507866994473)
    ·
      refine ⟨64635869002093130900245855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86181158669457507866994473 64635869002093130900245855)
      ·
        refine ⟨96953803503139696350368783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64635869002093130900245855 96953803503139696350368783)
        ·
          refine ⟨145430705254709544525553175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96953803503139696350368783 145430705254709544525553175)
          ·
            refine ⟨218146057882064316788329763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145430705254709544525553175 218146057882064316788329763)
            ·
              refine ⟨327219086823096475182494645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218146057882064316788329763 327219086823096475182494645)
              ·
                refine ⟨30676789389665294548358873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327219086823096475182494645 30676789389665294548358873)
                ·
                  refine ⟨23007592042248970911269155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30676789389665294548358873 23007592042248970911269155)
                  ·
                    refine ⟨34511388063373456366903733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23007592042248970911269155 34511388063373456366903733)
                    ·
                      refine ⟨3235442630941261534397225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34511388063373456366903733 3235442630941261534397225)
                      ·
                        rfl

theorem cell23_6301002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 5, 2, 1, 5].length) (baseStart_6301002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301002 prefixEnd_6301002 := by exact prefixLift 6301002
  have htrace : WordTrace (prefixWord ++ tailWord_6301002) baseStart_6301002 baseEnd_6301002 := by
    simpa [prefixWord, tailWord_6301002, baseEnd_6301002] using wordTrace_append hprefix tailTrace_6301002
  have hstable : (prefixWord ++ tailWord_6301002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301002).length < 2 ^ (prefixWord ++ tailWord_6301002).sum := by decide
  have hdescent : baseEnd_6301002 < baseStart_6301002 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301016 : List Nat := [2, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2]
def baseStart_6301016 : Nat := 118140960795 + 6301016 * 2 ^ 59
def prefixEnd_6301016 : Nat := 4983230072969 + 3 ^ 40 * 6301016 * 2
def baseEnd_6301016 : Nat := 3235449819670424479622161

theorem tailTrace_6301016 : CollatzResearch.WordTrace tailWord_6301016 prefixEnd_6301016 3235449819670424479622161 := by
  unfold tailWord_6301016
  simp only [CollatzResearch.WordTrace]
  refine ⟨114908466870251317351497451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153211289160335089801996601 114908466870251317351497451)
  ·
    refine ⟨172362700305376976027246177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114908466870251317351497451 172362700305376976027246177)
    ·
      refine ⟨129272025229032732020434633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172362700305376976027246177 129272025229032732020434633)
      ·
        refine ⟨96954018921774549015325975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129272025229032732020434633 96954018921774549015325975)
        ·
          refine ⟨145431028382661823522988963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96954018921774549015325975 145431028382661823522988963)
          ·
            refine ⟨218146542573992735284483445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145431028382661823522988963 218146542573992735284483445)
            ·
              refine ⟨20451238366311818932920323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 218146542573992735284483445 20451238366311818932920323)
              ·
                refine ⟨30676857549467728399380485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20451238366311818932920323 30676857549467728399380485)
                ·
                  refine ⟨5751910790525199074883841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30676857549467728399380485 5751910790525199074883841)
                  ·
                    refine ⟨4313933092893899306162881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751910790525199074883841 4313933092893899306162881)
                    ·
                      refine ⟨3235449819670424479622161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313933092893899306162881 3235449819670424479622161)
                      ·
                        rfl

theorem cell23_6301016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 1, 4, 2, 2].length) (baseStart_6301016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301016 prefixEnd_6301016 := by exact prefixLift 6301016
  have htrace : WordTrace (prefixWord ++ tailWord_6301016) baseStart_6301016 baseEnd_6301016 := by
    simpa [prefixWord, tailWord_6301016, baseEnd_6301016] using wordTrace_append hprefix tailTrace_6301016
  have hstable : (prefixWord ++ tailWord_6301016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301016).length < 2 ^ (prefixWord ++ tailWord_6301016).sum := by decide
  have hdescent : baseEnd_6301016 < baseStart_6301016 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301052 : List Nat := [2, 2, 2, 1, 1, 1, 3, 3, 1, 7]
def baseStart_6301052 : Nat := 118140960795 + 6301052 * 2 ^ 59
def prefixEnd_6301052 : Nat := 4983230072969 + 3 ^ 40 * 6301052 * 2
def baseEnd_6301052 : Nat := 1078489434991328779590665

theorem tailTrace_6301052 : CollatzResearch.WordTrace tailWord_6301052 prefixEnd_6301052 1078489434991328779590665 := by
  unfold tailWord_6301052
  simp only [CollatzResearch.WordTrace]
  refine ⟨114909123384186106425652705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153212164512248141900870273 114909123384186106425652705)
  ·
    refine ⟨86181842538139579819239529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114909123384186106425652705 86181842538139579819239529)
    ·
      refine ⟨64636381903604684864429647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86181842538139579819239529 64636381903604684864429647)
      ·
        refine ⟨96954572855407027296644471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64636381903604684864429647 96954572855407027296644471)
        ·
          refine ⟨145431859283110540944966707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96954572855407027296644471 145431859283110540944966707)
          ·
            refine ⟨218147788924665811417450061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145431859283110540944966707 218147788924665811417450061)
            ·
              refine ⟨81805420846749679281543773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218147788924665811417450061 81805420846749679281543773)
              ·
                refine ⟨30677032817531129730578915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81805420846749679281543773 30677032817531129730578915)
                ·
                  refine ⟨46015549226296694595868373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30677032817531129730578915 46015549226296694595868373)
                  ·
                    refine ⟨1078489434991328779590665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46015549226296694595868373 1078489434991328779590665)
                    ·
                      rfl

theorem cell23_6301052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 3, 3, 1, 7].length) (baseStart_6301052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301052 prefixEnd_6301052 := by exact prefixLift 6301052
  have htrace : WordTrace (prefixWord ++ tailWord_6301052) baseStart_6301052 baseEnd_6301052 := by
    simpa [prefixWord, tailWord_6301052, baseEnd_6301052] using wordTrace_append hprefix tailTrace_6301052
  have hstable : (prefixWord ++ tailWord_6301052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301052).length < 2 ^ (prefixWord ++ tailWord_6301052).sum := by decide
  have hdescent : baseEnd_6301052 < baseStart_6301052 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301084 : List Nat := [2, 2, 3, 4, 1, 2, 2, 1, 2, 2, 2]
def baseStart_6301084 : Nat := 118140960795 + 6301084 * 2 ^ 59
def prefixEnd_6301084 : Nat := 4983230072969 + 3 ^ 40 * 6301084 * 2
def baseEnd_6301084 : Nat := 3235484736354930213571849

theorem tailTrace_6301084 : CollatzResearch.WordTrace tailWord_6301084 prefixEnd_6301084 3235484736354930213571849 := by
  unfold tailWord_6301084
  simp only [CollatzResearch.WordTrace]
  refine ⟨114909706952128141158235153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153212942602837521544313537 114909706952128141158235153)
  ·
    refine ⟨86182280214096105868676365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114909706952128141158235153 86182280214096105868676365)
    ·
      refine ⟨32318355080286039700753637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86182280214096105868676365 32318355080286039700753637)
      ·
        refine ⟨6059691577553632443891307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32318355080286039700753637 6059691577553632443891307)
        ·
          refine ⟨9089537366330448665836961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6059691577553632443891307 9089537366330448665836961)
          ·
            refine ⟨6817153024747836499377721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9089537366330448665836961 6817153024747836499377721)
            ·
              refine ⟨5112864768560877374533291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6817153024747836499377721 5112864768560877374533291)
              ·
                refine ⟨7669297152841316061799937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112864768560877374533291 7669297152841316061799937)
                ·
                  refine ⟨5751972864630987046349953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7669297152841316061799937 5751972864630987046349953)
                  ·
                    refine ⟨4313979648473240284762465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5751972864630987046349953 4313979648473240284762465)
                    ·
                      refine ⟨3235484736354930213571849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4313979648473240284762465 3235484736354930213571849)
                      ·
                        rfl

theorem cell23_6301084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 2, 2, 1, 2, 2, 2].length) (baseStart_6301084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301084 prefixEnd_6301084 := by exact prefixLift 6301084
  have htrace : WordTrace (prefixWord ++ tailWord_6301084) baseStart_6301084 baseEnd_6301084 := by
    simpa [prefixWord, tailWord_6301084, baseEnd_6301084] using wordTrace_append hprefix tailTrace_6301084
  have hstable : (prefixWord ++ tailWord_6301084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301084).length < 2 ^ (prefixWord ++ tailWord_6301084).sum := by decide
  have hdescent : baseEnd_6301084 < baseStart_6301084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301112 : List Nat := [2, 1, 2, 1, 2, 2, 2, 1, 10]
def baseStart_6301112 : Nat := 118140960795 + 6301112 * 2 ^ 59
def prefixEnd_6301112 : Nat := 4983230072969 + 3 ^ 40 * 6301112 * 2
def baseEnd_6301112 : Nat := 359499901534806233780191

theorem tailTrace_6301112 : CollatzResearch.WordTrace tailWord_6301112 prefixEnd_6301112 359499901534806233780191 := by
  unfold tailWord_6301112
  simp only [CollatzResearch.WordTrace]
  refine ⟨114910217574077421549244795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153213623432103228732326393 114910217574077421549244795)
  ·
    refine ⟨172365326361116132323867193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114910217574077421549244795 172365326361116132323867193)
    ·
      refine ⟨129273994770837099242900395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172365326361116132323867193 129273994770837099242900395)
      ·
        refine ⟨193910992156255648864350593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129273994770837099242900395 193910992156255648864350593)
        ·
          refine ⟨145433244117191736648262945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193910992156255648864350593 145433244117191736648262945)
          ·
            refine ⟨109074933087893802486197209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145433244117191736648262945 109074933087893802486197209)
            ·
              refine ⟨81806199815920351864647907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109074933087893802486197209 81806199815920351864647907)
              ·
                refine ⟨122709299723880527796971861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81806199815920351864647907 122709299723880527796971861)
                ·
                  refine ⟨359499901534806233780191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 122709299723880527796971861 359499901534806233780191)
                  ·
                    rfl

theorem cell23_6301112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 1, 10].length) (baseStart_6301112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301112 prefixEnd_6301112 := by exact prefixLift 6301112
  have htrace : WordTrace (prefixWord ++ tailWord_6301112) baseStart_6301112 baseEnd_6301112 := by
    simpa [prefixWord, tailWord_6301112, baseEnd_6301112] using wordTrace_append hprefix tailTrace_6301112
  have hstable : (prefixWord ++ tailWord_6301112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301112).length < 2 ^ (prefixWord ++ tailWord_6301112).sum := by decide
  have hdescent : baseEnd_6301112 < baseStart_6301112 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301176 : List Nat := [2, 1, 2, 1, 1, 6, 1, 3, 1, 5]
def baseStart_6301176 : Nat := 118140960795 + 6301176 * 2 ^ 59
def prefixEnd_6301176 : Nat := 4983230072969 + 3 ^ 40 * 6301176 * 2
def baseEnd_6301176 : Nat := 1078510658858381284540475

theorem tailTrace_6301176 : CollatzResearch.WordTrace tailWord_6301176 prefixEnd_6301176 1078510658858381284540475 := by
  unfold tailWord_6301176
  simp only [CollatzResearch.WordTrace]
  refine ⟨114911384709961491014409691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153215179613281988019212921 114911384709961491014409691)
  ·
    refine ⟨172367077064942236521614537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114911384709961491014409691 172367077064942236521614537)
    ·
      refine ⟨129275307798706677391210903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172367077064942236521614537 129275307798706677391210903)
      ·
        refine ⟨193912961698060016086816355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129275307798706677391210903 193912961698060016086816355)
        ·
          refine ⟨290869442547090024130224533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193912961698060016086816355 290869442547090024130224533)
          ·
            refine ⟨13634505119394844881104275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 290869442547090024130224533 13634505119394844881104275)
            ·
              refine ⟨20451757679092267321656413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13634505119394844881104275 20451757679092267321656413)
              ·
                refine ⟨7669409129659600245621155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20451757679092267321656413 7669409129659600245621155)
                ·
                  refine ⟨11504113694489400368431733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669409129659600245621155 11504113694489400368431733)
                  ·
                    refine ⟨1078510658858381284540475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11504113694489400368431733 1078510658858381284540475)
                    ·
                      rfl

theorem cell23_6301176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 3, 1, 5].length) (baseStart_6301176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301176 prefixEnd_6301176 := by exact prefixLift 6301176
  have htrace : WordTrace (prefixWord ++ tailWord_6301176) baseStart_6301176 baseEnd_6301176 := by
    simpa [prefixWord, tailWord_6301176, baseEnd_6301176] using wordTrace_append hprefix tailTrace_6301176
  have hstable : (prefixWord ++ tailWord_6301176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301176).length < 2 ^ (prefixWord ++ tailWord_6301176).sum := by decide
  have hdescent : baseEnd_6301176 < baseStart_6301176 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301197 : List Nat := [1, 7, 1, 1, 2, 1, 3, 1, 6]
def baseStart_6301197 : Nat := 118140960795 + 6301197 * 2 ^ 59
def prefixEnd_6301197 : Nat := 4983230072969 + 3 ^ 40 * 6301197 * 2
def baseEnd_6301197 : Nat := 359504751074320919050981

theorem tailTrace_6301197 : CollatzResearch.WordTrace tailWord_6301197 prefixEnd_6301197 359504751074320919050981 := by
  unfold tailWord_6301197
  simp only [CollatzResearch.WordTrace]
  refine ⟨229823535352846902615333845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153215690235231268410222563 229823535352846902615333845)
  ·
    refine ⟨5386489109832349280046887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 229823535352846902615333845 5386489109832349280046887)
    ·
      refine ⟨8079733664748523920070331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5386489109832349280046887 8079733664748523920070331)
      ·
        refine ⟨12119600497122785880105497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8079733664748523920070331 12119600497122785880105497)
        ·
          refine ⟨9089700372842089410079123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12119600497122785880105497 9089700372842089410079123)
          ·
            refine ⟨13634550559263134115118685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9089700372842089410079123 13634550559263134115118685)
            ·
              refine ⟨5112956459723675293169507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13634550559263134115118685 5112956459723675293169507)
              ·
                refine ⟨7669434689585512939754261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5112956459723675293169507 7669434689585512939754261)
                ·
                  refine ⟨359504751074320919050981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7669434689585512939754261 359504751074320919050981)
                  ·
                    rfl

theorem cell23_6301197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 3, 1, 6].length) (baseStart_6301197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301197 prefixEnd_6301197 := by exact prefixLift 6301197
  have htrace : WordTrace (prefixWord ++ tailWord_6301197) baseStart_6301197 baseEnd_6301197 := by
    simpa [prefixWord, tailWord_6301197, baseEnd_6301197] using wordTrace_append hprefix tailTrace_6301197
  have hstable : (prefixWord ++ tailWord_6301197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301197).length < 2 ^ (prefixWord ++ tailWord_6301197).sum := by decide
  have hdescent : baseEnd_6301197 < baseStart_6301197 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301213 : List Nat := [1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_6301213 : Nat := 118140960795 + 6301213 * 2 ^ 59
def prefixEnd_6301213 : Nat := 4983230072969 + 3 ^ 40 * 6301213 * 2
def baseEnd_6301213 : Nat := 3235550975359360208858755

theorem tailTrace_6301213 : CollatzResearch.WordTrace tailWord_6301213 prefixEnd_6301213 3235550975359360208858755 := by
  unfold tailWord_6301213
  simp only [CollatzResearch.WordTrace]
  refine ⟨229824118920788937347916293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153216079280525958231944195 229824118920788937347916293)
  ·
    refine ⟨43092022297647925752734305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229824118920788937347916293 43092022297647925752734305)
    ·
      refine ⟨32319016723235944314550729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43092022297647925752734305 32319016723235944314550729)
      ·
        refine ⟨24239262542426958235913047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32319016723235944314550729 24239262542426958235913047)
        ·
          refine ⟨36358893813640437353869571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24239262542426958235913047 36358893813640437353869571)
          ·
            refine ⟨54538340720460656030804357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36358893813640437353869571 54538340720460656030804357)
            ·
              refine ⟨10225938885086373005775817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54538340720460656030804357 10225938885086373005775817)
              ·
                refine ⟨7669454163814779754331863, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10225938885086373005775817 7669454163814779754331863)
                ·
                  refine ⟨11504181245722169631497795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669454163814779754331863 11504181245722169631497795)
                  ·
                    refine ⟨17256271868583254447246693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11504181245722169631497795 17256271868583254447246693)
                    ·
                      refine ⟨3235550975359360208858755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17256271868583254447246693 3235550975359360208858755)
                      ·
                        rfl

theorem cell23_6301213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_6301213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301213 prefixEnd_6301213 := by exact prefixLift 6301213
  have htrace : WordTrace (prefixWord ++ tailWord_6301213) baseStart_6301213 baseEnd_6301213 := by
    simpa [prefixWord, tailWord_6301213, baseEnd_6301213] using wordTrace_append hprefix tailTrace_6301213
  have hstable : (prefixWord ++ tailWord_6301213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301213).length < 2 ^ (prefixWord ++ tailWord_6301213).sum := by decide
  have hdescent : baseEnd_6301213 < baseStart_6301213 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301224 : List Nat := [2, 1, 5, 2, 2, 2, 1, 3, 1, 1, 3]
def baseStart_6301224 : Nat := 118140960795 + 6301224 * 2 ^ 59
def prefixEnd_6301224 : Nat := 4983230072969 + 3 ^ 40 * 6301224 * 2
def baseEnd_6301224 : Nat := 3235556623646559665821205

theorem tailTrace_6301224 : CollatzResearch.WordTrace tailWord_6301224 prefixEnd_6301224 3235556623646559665821205 := by
  unfold tailWord_6301224
  simp only [CollatzResearch.WordTrace]
  refine ⟨114912260061874543113283363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153216346749166057484377817 114912260061874543113283363)
  ·
    refine ⟨172368390092811814669925045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114912260061874543113283363 172368390092811814669925045)
    ·
      refine ⟨16159536571201107625305473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 172368390092811814669925045 16159536571201107625305473)
      ·
        refine ⟨12119652428400830718979105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16159536571201107625305473 12119652428400830718979105)
        ·
          refine ⟨9089739321300623039234329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12119652428400830718979105 9089739321300623039234329)
          ·
            refine ⟨6817304490975467279425747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9089739321300623039234329 6817304490975467279425747)
            ·
              refine ⟨10225956736463200919138621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817304490975467279425747 10225956736463200919138621)
              ·
                refine ⟨3834733776173700344676983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10225956736463200919138621 3834733776173700344676983)
                ·
                  refine ⟨5752100664260550517015475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834733776173700344676983 5752100664260550517015475)
                  ·
                    refine ⟨8628150996390825775523213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5752100664260550517015475 8628150996390825775523213)
                    ·
                      refine ⟨3235556623646559665821205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8628150996390825775523213 3235556623646559665821205)
                      ·
                        rfl

theorem cell23_6301224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 2, 1, 3, 1, 1, 3].length) (baseStart_6301224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301224 prefixEnd_6301224 := by exact prefixLift 6301224
  have htrace : WordTrace (prefixWord ++ tailWord_6301224) baseStart_6301224 baseEnd_6301224 := by
    simpa [prefixWord, tailWord_6301224, baseEnd_6301224] using wordTrace_append hprefix tailTrace_6301224
  have hstable : (prefixWord ++ tailWord_6301224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301224).length < 2 ^ (prefixWord ++ tailWord_6301224).sum := by decide
  have hdescent : baseEnd_6301224 < baseStart_6301224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301226 : List Nat := [3, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4]
def baseStart_6301226 : Nat := 118140960795 + 6301226 * 2 ^ 59
def prefixEnd_6301226 : Nat := 4983230072969 + 3 ^ 40 * 6301226 * 2
def baseEnd_6301226 : Nat := 3235557650607868657996195

theorem tailTrace_6301226 : CollatzResearch.WordTrace tailWord_6301226 prefixEnd_6301226 3235557650607868657996195 := by
  unfold tailWord_6301226
  simp only [CollatzResearch.WordTrace]
  refine ⟨57456148267435460142034883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153216395379827893712093021 57456148267435460142034883)
  ·
    refine ⟨86184222401153190213052325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57456148267435460142034883 86184222401153190213052325)
    ·
      refine ⟨16159541700216223164947311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86184222401153190213052325 16159541700216223164947311)
      ·
        refine ⟨24239312550324334747420967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16159541700216223164947311 24239312550324334747420967)
        ·
          refine ⟨36358968825486502121131451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24239312550324334747420967 36358968825486502121131451)
          ·
            refine ⟨54538453238229753181697177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36358968825486502121131451 54538453238229753181697177)
            ·
              refine ⟨40903839928672314886272883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54538453238229753181697177 40903839928672314886272883)
              ·
                refine ⟨61355759893008472329409325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40903839928672314886272883 61355759893008472329409325)
                ·
                  refine ⟨23008409959878177123528497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61355759893008472329409325 23008409959878177123528497)
                  ·
                    refine ⟨17256307469908632842646373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23008409959878177123528497 17256307469908632842646373)
                    ·
                      refine ⟨3235557650607868657996195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17256307469908632842646373 3235557650607868657996195)
                      ·
                        rfl

theorem cell23_6301226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_6301226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301226 prefixEnd_6301226 := by exact prefixLift 6301226
  have htrace : WordTrace (prefixWord ++ tailWord_6301226) baseStart_6301226 baseEnd_6301226 := by
    simpa [prefixWord, tailWord_6301226, baseEnd_6301226] using wordTrace_append hprefix tailTrace_6301226
  have hstable : (prefixWord ++ tailWord_6301226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301226).length < 2 ^ (prefixWord ++ tailWord_6301226).sum := by decide
  have hdescent : baseEnd_6301226 < baseStart_6301226 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301256 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2]
def baseStart_6301256 : Nat := 118140960795 + 6301256 * 2 ^ 59
def prefixEnd_6301256 : Nat := 4983230072969 + 3 ^ 40 * 6301256 * 2
def baseEnd_6301256 : Nat := 3235573055027503540621057

theorem tailTrace_6301256 : CollatzResearch.WordTrace tailWord_6301256 prefixEnd_6301256 3235573055027503540621057 := by
  unfold tailWord_6301256
  simp only [CollatzResearch.WordTrace]
  refine ⟨114912843629816577845865811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153217124839755437127821081 114912843629816577845865811)
  ·
    refine ⟨172369265444724866768798717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114912843629816577845865811 172369265444724866768798717)
    ·
      refine ⟨64638474541771825038299519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172369265444724866768798717 64638474541771825038299519)
      ·
        refine ⟨96957711812657737557449279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64638474541771825038299519 96957711812657737557449279)
        ·
          refine ⟨145436567718986606336173919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96957711812657737557449279 145436567718986606336173919)
          ·
            refine ⟨218154851578479909504260879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145436567718986606336173919 218154851578479909504260879)
            ·
              refine ⟨327232277367719864256391319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218154851578479909504260879 327232277367719864256391319)
              ·
                refine ⟨490848416051579796384586979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327232277367719864256391319 490848416051579796384586979)
                ·
                  refine ⟨736272624077369694576880469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 490848416051579796384586979 736272624077369694576880469)
                  ·
                    refine ⟨4314097406703338054161409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 736272624077369694576880469 4314097406703338054161409)
                    ·
                      refine ⟨3235573055027503540621057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314097406703338054161409 3235573055027503540621057)
                      ·
                        rfl

theorem cell23_6301256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_6301256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301256 prefixEnd_6301256 := by exact prefixLift 6301256
  have htrace : WordTrace (prefixWord ++ tailWord_6301256) baseStart_6301256 baseEnd_6301256 := by
    simpa [prefixWord, tailWord_6301256, baseEnd_6301256] using wordTrace_append hprefix tailTrace_6301256
  have hstable : (prefixWord ++ tailWord_6301256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301256).length < 2 ^ (prefixWord ++ tailWord_6301256).sum := by decide
  have hdescent : baseEnd_6301256 < baseStart_6301256 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301269 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 8]
def baseStart_6301269 : Nat := 118140960795 + 6301269 * 2 ^ 59
def prefixEnd_6301269 : Nat := 4983230072969 + 3 ^ 40 * 6301269 * 2
def baseEnd_6301269 : Nat := 3235579730276011989758497

theorem tailTrace_6301269 : CollatzResearch.WordTrace tailWord_6301269 prefixEnd_6301269 3235579730276011989758497 := by
  unfold tailWord_6301269
  simp only [CollatzResearch.WordTrace]
  refine ⟨229826161408586058911954861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153217440939057372607969907 229826161408586058911954861)
  ·
    refine ⟨86184810528219772091983073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229826161408586058911954861 86184810528219772091983073)
    ·
      refine ⟨64638607896164829068987305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86184810528219772091983073 64638607896164829068987305)
      ·
        refine ⟨48478955922123621801740479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64638607896164829068987305 48478955922123621801740479)
        ·
          refine ⟨72718433883185432702610719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48478955922123621801740479 72718433883185432702610719)
          ·
            refine ⟨109077650824778149053916079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72718433883185432702610719 109077650824778149053916079)
            ·
              refine ⟨163616476237167223580874119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109077650824778149053916079 163616476237167223580874119)
              ·
                refine ⟨245424714355750835371311179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163616476237167223580874119 245424714355750835371311179)
                ·
                  refine ⟨368137071533626253056966769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 245424714355750835371311179 368137071533626253056966769)
                  ·
                    refine ⟨276102803650219689792725077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 368137071533626253056966769 276102803650219689792725077)
                    ·
                      refine ⟨3235579730276011989758497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 276102803650219689792725077 3235579730276011989758497)
                      ·
                        rfl

theorem cell23_6301269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_6301269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301269 prefixEnd_6301269 := by exact prefixLift 6301269
  have htrace : WordTrace (prefixWord ++ tailWord_6301269) baseStart_6301269 baseEnd_6301269 := by
    simpa [prefixWord, tailWord_6301269, baseEnd_6301269] using wordTrace_append hprefix tailTrace_6301269
  have hstable : (prefixWord ++ tailWord_6301269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301269).length < 2 ^ (prefixWord ++ tailWord_6301269).sum := by decide
  have hdescent : baseEnd_6301269 < baseStart_6301269 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301279 : List Nat := [1, 1, 2, 3, 1, 1, 1, 1, 6, 6]
def baseStart_6301279 : Nat := 118140960795 + 6301279 * 2 ^ 59
def prefixEnd_6301279 : Nat := 4983230072969 + 3 ^ 40 * 6301279 * 2
def baseEnd_6301279 : Nat := 1078528288360852316877817

theorem tailTrace_6301279 : CollatzResearch.WordTrace tailWord_6301279 prefixEnd_6301279 1078528288360852316877817 := by
  unfold tailWord_6301279
  simp only [CollatzResearch.WordTrace]
  refine ⟨229826526138549830619818891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153217684092366553746545927 229826526138549830619818891)
  ·
    refine ⟨344739789207824745929728337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229826526138549830619818891 344739789207824745929728337)
    ·
      refine ⟨258554841905868559447296253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344739789207824745929728337 258554841905868559447296253)
      ·
        refine ⟨96958065714700709792736095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258554841905868559447296253 96958065714700709792736095)
        ·
          refine ⟨145437098572051064689104143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96958065714700709792736095 145437098572051064689104143)
          ·
            refine ⟨218155647858076597033656215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145437098572051064689104143 218155647858076597033656215)
            ·
              refine ⟨327233471787114895550484323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218155647858076597033656215 327233471787114895550484323)
              ·
                refine ⟨490850207680672343325726485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327233471787114895550484323 490850207680672343325726485)
                ·
                  refine ⟨23008603485031516093393429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 490850207680672343325726485 23008603485031516093393429)
                  ·
                    refine ⟨1078528288360852316877817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23008603485031516093393429 1078528288360852316877817)
                    ·
                      rfl

theorem cell23_6301279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6, 6].length) (baseStart_6301279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301279 prefixEnd_6301279 := by exact prefixLift 6301279
  have htrace : WordTrace (prefixWord ++ tailWord_6301279) baseStart_6301279 baseEnd_6301279 := by
    simpa [prefixWord, tailWord_6301279, baseEnd_6301279] using wordTrace_append hprefix tailTrace_6301279
  have hstable : (prefixWord ++ tailWord_6301279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301279).length < 2 ^ (prefixWord ++ tailWord_6301279).sum := by decide
  have hdescent : baseEnd_6301279 < baseStart_6301279 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301326 : List Nat := [4, 1, 1, 3, 1, 2, 1, 1, 9]
def baseStart_6301326 : Nat := 118140960795 + 6301326 * 2 ^ 59
def prefixEnd_6301326 : Nat := 4983230072969 + 3 ^ 40 * 6301326 * 2
def baseEnd_6301326 : Nat := 359512110963702029638415

theorem tailTrace_6301326 : CollatzResearch.WordTrace tailWord_6301326 prefixEnd_6301326 359512110963702029638415 := by
  unfold tailWord_6301326
  simp only [CollatzResearch.WordTrace]
  refine ⟨28728530046172444705847479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153218826912919705097853221 28728530046172444705847479)
  ·
    refine ⟨43092795069258667058771219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28728530046172444705847479 43092795069258667058771219)
    ·
      refine ⟨64639192603888000588156829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43092795069258667058771219 64639192603888000588156829)
      ·
        refine ⟨24239697226458000220558811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64639192603888000588156829 24239697226458000220558811)
        ·
          refine ⟨36359545839687000330838217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24239697226458000220558811 36359545839687000330838217)
          ·
            refine ⟨27269659379765250248128663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36359545839687000330838217 27269659379765250248128663)
            ·
              refine ⟨40904489069647875372192995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27269659379765250248128663 40904489069647875372192995)
              ·
                refine ⟨61356733604471813058289493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40904489069647875372192995 61356733604471813058289493)
                ·
                  refine ⟨359512110963702029638415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61356733604471813058289493 359512110963702029638415)
                  ·
                    rfl

theorem cell23_6301326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 2, 1, 1, 9].length) (baseStart_6301326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301326 prefixEnd_6301326 := by exact prefixLift 6301326
  have htrace : WordTrace (prefixWord ++ tailWord_6301326) baseStart_6301326 baseEnd_6301326 := by
    simpa [prefixWord, tailWord_6301326, baseEnd_6301326] using wordTrace_append hprefix tailTrace_6301326
  have hstable : (prefixWord ++ tailWord_6301326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301326).length < 2 ^ (prefixWord ++ tailWord_6301326).sum := by decide
  have hdescent : baseEnd_6301326 < baseStart_6301326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301376 : List Nat := [2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4]
def baseStart_6301376 : Nat := 118140960795 + 6301376 * 2 ^ 59
def prefixEnd_6301376 : Nat := 4983230072969 + 3 ^ 40 * 6301376 * 2
def baseEnd_6301376 : Nat := 3235634672706043071120505

theorem tailTrace_6301376 : CollatzResearch.WordTrace tailWord_6301376 prefixEnd_6301376 3235634672706043071120505 := by
  unfold tailWord_6301376
  simp only [CollatzResearch.WordTrace]
  refine ⟨114915032009599208093049991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153220042679465610790733321 114915032009599208093049991)
  ·
    refine ⟨172372548014398812139574987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114915032009599208093049991 172372548014398812139574987)
    ·
      refine ⟨258558822021598218209362481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172372548014398812139574987 258558822021598218209362481)
      ·
        refine ⟨193919116516198663657021861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258558822021598218209362481 193919116516198663657021861)
        ·
          refine ⟨36359834346787249435691599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193919116516198663657021861 36359834346787249435691599)
          ·
            refine ⟨54539751520180874153537399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36359834346787249435691599 54539751520180874153537399)
            ·
              refine ⟨81809627280271311230306099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54539751520180874153537399 81809627280271311230306099)
              ·
                refine ⟨122714440920406966845459149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81809627280271311230306099 122714440920406966845459149)
                ·
                  refine ⟨46017915345152612567047181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122714440920406966845459149 46017915345152612567047181)
                  ·
                    refine ⟨17256718254432229712642693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46017915345152612567047181 17256718254432229712642693)
                    ·
                      refine ⟨3235634672706043071120505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17256718254432229712642693 3235634672706043071120505)
                      ·
                        rfl

theorem cell23_6301376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_6301376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301376 prefixEnd_6301376 := by exact prefixLift 6301376
  have htrace : WordTrace (prefixWord ++ tailWord_6301376) baseStart_6301376 baseEnd_6301376 := by
    simpa [prefixWord, tailWord_6301376, baseEnd_6301376] using wordTrace_append hprefix tailTrace_6301376
  have hstable : (prefixWord ++ tailWord_6301376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301376).length < 2 ^ (prefixWord ++ tailWord_6301376).sum := by decide
  have hdescent : baseEnd_6301376 < baseStart_6301376 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301420 : List Nat := [2, 2, 1, 1, 2, 2, 2, 6, 1, 4]
def baseStart_6301420 : Nat := 118140960795 + 6301420 * 2 ^ 59
def prefixEnd_6301420 : Nat := 4983230072969 + 3 ^ 40 * 6301420 * 2
def baseEnd_6301420 : Nat := 1078552421951613632990101

theorem tailTrace_6301420 : CollatzResearch.WordTrace tailWord_6301420 prefixEnd_6301420 1078552421951613632990101 := by
  unfold tailWord_6301420
  simp only [CollatzResearch.WordTrace]
  refine ⟨114915834415519505850350857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153221112554026007800467809 114915834415519505850350857)
  ·
    refine ⟨86186875811639629387763143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114915834415519505850350857 86186875811639629387763143)
    ·
      refine ⟨129280313717459444081644715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86186875811639629387763143 129280313717459444081644715)
      ·
        refine ⟨193920470576189166122467073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129280313717459444081644715 193920470576189166122467073)
        ·
          refine ⟨145440352932141874591850305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193920470576189166122467073 145440352932141874591850305)
          ·
            refine ⟨109080264699106405943887729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145440352932141874591850305 109080264699106405943887729)
            ·
              refine ⟨81810198524329804457915797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109080264699106405943887729 81810198524329804457915797)
              ·
                refine ⟨3834853055827959583964803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81810198524329804457915797 3834853055827959583964803)
                ·
                  refine ⟨5752279583741939375947205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3834853055827959583964803 5752279583741939375947205)
                  ·
                    refine ⟨1078552421951613632990101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752279583741939375947205 1078552421951613632990101)
                    ·
                      rfl

theorem cell23_6301420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 6, 1, 4].length) (baseStart_6301420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301420 prefixEnd_6301420 := by exact prefixLift 6301420
  have htrace : WordTrace (prefixWord ++ tailWord_6301420) baseStart_6301420 baseEnd_6301420 := by
    simpa [prefixWord, tailWord_6301420, baseEnd_6301420] using wordTrace_append hprefix tailTrace_6301420
  have hstable : (prefixWord ++ tailWord_6301420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301420).length < 2 ^ (prefixWord ++ tailWord_6301420).sum := by decide
  have hdescent : baseEnd_6301420 < baseStart_6301420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301447 : List Nat := [1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3]
def baseStart_6301447 : Nat := 118140960795 + 6301447 * 2 ^ 59
def prefixEnd_6301447 : Nat := 4983230072969 + 3 ^ 40 * 6301447 * 2
def baseEnd_6301447 : Nat := 3235671129832512293332679

theorem tailTrace_6301447 : CollatzResearch.WordTrace tailWord_6301447 prefixEnd_6301447 3235671129832512293332679 := by
  unfold tailWord_6301447
  simp only [CollatzResearch.WordTrace]
  refine ⟨229832653601941195311934595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153221769067960796874623063 229832653601941195311934595)
  ·
    refine ⟨344748980402911792967901893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229832653601941195311934595 344748980402911792967901893)
    ·
      refine ⟨64640433825545961181481605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344748980402911792967901893 64640433825545961181481605)
      ·
        refine ⟨12120081342289867721527801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64640433825545961181481605 12120081342289867721527801)
        ·
          refine ⟨9090061006717400791145851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12120081342289867721527801 9090061006717400791145851)
          ·
            refine ⟨13635091510076101186718777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090061006717400791145851 13635091510076101186718777)
            ·
              refine ⟨10226318632557075890039083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635091510076101186718777 10226318632557075890039083)
              ·
                refine ⟨15339477948835613835058625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226318632557075890039083 15339477948835613835058625)
                ·
                  refine ⟨11504608461626710376293969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15339477948835613835058625 11504608461626710376293969)
                  ·
                    refine ⟨8628456346220032782220477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11504608461626710376293969 8628456346220032782220477)
                    ·
                      refine ⟨3235671129832512293332679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8628456346220032782220477 3235671129832512293332679)
                      ·
                        rfl

theorem cell23_6301447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_6301447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301447 prefixEnd_6301447 := by exact prefixLift 6301447
  have htrace : WordTrace (prefixWord ++ tailWord_6301447) baseStart_6301447 baseEnd_6301447 := by
    simpa [prefixWord, tailWord_6301447, baseEnd_6301447] using wordTrace_append hprefix tailTrace_6301447
  have hstable : (prefixWord ++ tailWord_6301447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301447).length < 2 ^ (prefixWord ++ tailWord_6301447).sum := by decide
  have hdescent : baseEnd_6301447 < baseStart_6301447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301494 : List Nat := [5, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3]
def baseStart_6301494 : Nat := 118140960795 + 6301494 * 2 ^ 59
def prefixEnd_6301494 : Nat := 4983230072969 + 3 ^ 40 * 6301494 * 2
def baseEnd_6301494 : Nat := 3235695263423273609444963

theorem tailTrace_6301494 : CollatzResearch.WordTrace tailWord_6301494 prefixEnd_6301494 3235695263423273609444963 := by
  unfold tailWord_6301494
  simp only [CollatzResearch.WordTrace]
  refine ⟨14364647989548182646180971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153222911888513948225930357 14364647989548182646180971)
  ·
    refine ⟨21546971984322273969271457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14364647989548182646180971 21546971984322273969271457)
    ·
      refine ⟨16160228988241705476953593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21546971984322273969271457 16160228988241705476953593)
      ·
        refine ⟨12120171741181279107715195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16160228988241705476953593 12120171741181279107715195)
        ·
          refine ⟨18180257611771918661572793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12120171741181279107715195 18180257611771918661572793)
          ·
            refine ⟨13635193208828938996179595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18180257611771918661572793 13635193208828938996179595)
            ·
              refine ⟨20452789813243408494269393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635193208828938996179595 20452789813243408494269393)
              ·
                refine ⟨15339592359932556370702045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20452789813243408494269393 15339592359932556370702045)
                ·
                  refine ⟨5752347134974708639013267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15339592359932556370702045 5752347134974708639013267)
                  ·
                    refine ⟨8628520702462062958519901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5752347134974708639013267 8628520702462062958519901)
                    ·
                      refine ⟨3235695263423273609444963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8628520702462062958519901 3235695263423273609444963)
                      ·
                        rfl

theorem cell23_6301494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 1, 2, 3, 1, 3].length) (baseStart_6301494 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301494 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301494 prefixEnd_6301494 := by exact prefixLift 6301494
  have htrace : WordTrace (prefixWord ++ tailWord_6301494) baseStart_6301494 baseEnd_6301494 := by
    simpa [prefixWord, tailWord_6301494, baseEnd_6301494] using wordTrace_append hprefix tailTrace_6301494
  have hstable : (prefixWord ++ tailWord_6301494).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301494).length < 2 ^ (prefixWord ++ tailWord_6301494).sum := by decide
  have hdescent : baseEnd_6301494 < baseStart_6301494 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301513 : List Nat := [1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 4]
def baseStart_6301513 : Nat := 118140960795 + 6301513 * 2 ^ 59
def prefixEnd_6301513 : Nat := 4983230072969 + 3 ^ 40 * 6301513 * 2
def baseEnd_6301513 : Nat := 3235705019555709035107375

theorem tailTrace_6301513 : CollatzResearch.WordTrace tailWord_6301513 prefixEnd_6301513 3235705019555709035107375 := by
  unfold tailWord_6301513
  simp only [CollatzResearch.WordTrace]
  refine ⟨229835060819702088583837193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153223373879801392389224795 229835060819702088583837193)
  ·
    refine ⟨172376295614776566437877895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229835060819702088583837193 172376295614776566437877895)
    ·
      refine ⟨258564443422164849656816843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172376295614776566437877895 258564443422164849656816843)
      ·
        refine ⟨387846665133247274485225265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258564443422164849656816843 387846665133247274485225265)
        ·
          refine ⟨290884998849935455863918949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387846665133247274485225265 290884998849935455863918949)
          ·
            refine ⟨54540937284362897974484803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290884998849935455863918949 54540937284362897974484803)
            ·
              refine ⟨81811405926544346961727205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54540937284362897974484803 81811405926544346961727205)
              ·
                refine ⟨15339638611227065055323851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81811405926544346961727205 15339638611227065055323851)
                ·
                  refine ⟨23009457916840597582985777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15339638611227065055323851 23009457916840597582985777)
                  ·
                    refine ⟨17257093437630448187239333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23009457916840597582985777 17257093437630448187239333)
                    ·
                      refine ⟨3235705019555709035107375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17257093437630448187239333 3235705019555709035107375)
                      ·
                        rfl

theorem cell23_6301513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 4, 1, 2, 4].length) (baseStart_6301513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301513 prefixEnd_6301513 := by exact prefixLift 6301513
  have htrace : WordTrace (prefixWord ++ tailWord_6301513) baseStart_6301513 baseEnd_6301513 := by
    simpa [prefixWord, tailWord_6301513, baseEnd_6301513] using wordTrace_append hprefix tailTrace_6301513
  have hstable : (prefixWord ++ tailWord_6301513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301513).length < 2 ^ (prefixWord ++ tailWord_6301513).sum := by decide
  have hdescent : baseEnd_6301513 < baseStart_6301513 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301560 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2]
def baseStart_6301560 : Nat := 118140960795 + 6301560 * 2 ^ 59
def prefixEnd_6301560 : Nat := 4983230072969 + 3 ^ 40 * 6301560 * 2
def baseEnd_6301560 : Nat := 3235729153146470351219659

theorem tailTrace_6301560 : CollatzResearch.WordTrace tailWord_6301560 prefixEnd_6301560 3235729153146470351219659 := by
  unfold tailWord_6301560
  simp only [CollatzResearch.WordTrace]
  refine ⟨114918387525265907805399067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153224516700354543740532089 114918387525265907805399067)
  ·
    refine ⟨172377581287898861708098601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114918387525265907805399067 172377581287898861708098601)
    ·
      refine ⟨129283185965924146281073951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172377581287898861708098601 129283185965924146281073951)
      ·
        refine ⟨193924778948886219421610927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129283185965924146281073951 193924778948886219421610927)
        ·
          refine ⟨290887168423329329132416391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193924778948886219421610927 290887168423329329132416391)
          ·
            refine ⟨436330752634993993698624587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290887168423329329132416391 436330752634993993698624587)
            ·
              refine ⟨654496128952490990547936881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436330752634993993698624587 654496128952490990547936881)
              ·
                refine ⟨490872096714368242910952661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654496128952490990547936881 490872096714368242910952661)
                ·
                  refine ⟨11504814766743005693225453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 490872096714368242910952661 11504814766743005693225453)
                  ·
                    refine ⟨4314305537528627134959545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11504814766743005693225453 4314305537528627134959545)
                    ·
                      refine ⟨3235729153146470351219659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314305537528627134959545 3235729153146470351219659)
                      ·
                        rfl

theorem cell23_6301560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 7, 3, 2].length) (baseStart_6301560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301560 prefixEnd_6301560 := by exact prefixLift 6301560
  have htrace : WordTrace (prefixWord ++ tailWord_6301560) baseStart_6301560 baseEnd_6301560 := by
    simpa [prefixWord, tailWord_6301560, baseEnd_6301560] using wordTrace_append hprefix tailTrace_6301560
  have hstable : (prefixWord ++ tailWord_6301560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301560).length < 2 ^ (prefixWord ++ tailWord_6301560).sum := by decide
  have hdescent : baseEnd_6301560 < baseStart_6301560 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301577 : List Nat := [1, 2, 1, 1, 5, 1, 1, 5, 1, 3, 2]
def baseStart_6301577 : Nat := 118140960795 + 6301577 * 2 ^ 59
def prefixEnd_6301577 : Nat := 4983230072969 + 3 ^ 40 * 6301577 * 2
def baseEnd_6301577 : Nat := 3235737882317596784707081

theorem tailTrace_6301577 : CollatzResearch.WordTrace tailWord_6301577 prefixEnd_6301577 3235737882317596784707081 := by
  unfold tailWord_6301577
  simp only [CollatzResearch.WordTrace]
  refine ⟨229837395091470227514166985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153224930060980151676111323 229837395091470227514166985)
  ·
    refine ⟨172378046318602670635625239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229837395091470227514166985 172378046318602670635625239)
    ·
      refine ⟨258567069477904005953437859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172378046318602670635625239 258567069477904005953437859)
      ·
        refine ⟨387850604216856008930156789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258567069477904005953437859 387850604216856008930156789)
        ·
          refine ⟨36360994145330250837202199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 387850604216856008930156789 36360994145330250837202199)
          ·
            refine ⟨54541491217995376255803299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36360994145330250837202199 54541491217995376255803299)
            ·
              refine ⟨81812236826993064383704949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54541491217995376255803299 81812236826993064383704949)
              ·
                refine ⟨7669897202530599785972339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81812236826993064383704949 7669897202530599785972339)
                ·
                  refine ⟨11504845803795899678958509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669897202530599785972339 11504845803795899678958509)
                  ·
                    refine ⟨4314317176423462379609441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11504845803795899678958509 4314317176423462379609441)
                    ·
                      refine ⟨3235737882317596784707081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314317176423462379609441 3235737882317596784707081)
                      ·
                        rfl

theorem cell23_6301577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 5, 1, 3, 2].length) (baseStart_6301577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301577 prefixEnd_6301577 := by exact prefixLift 6301577
  have htrace : WordTrace (prefixWord ++ tailWord_6301577) baseStart_6301577 baseEnd_6301577 := by
    simpa [prefixWord, tailWord_6301577, baseEnd_6301577] using wordTrace_append hprefix tailTrace_6301577
  have hstable : (prefixWord ++ tailWord_6301577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301577).length < 2 ^ (prefixWord ++ tailWord_6301577).sum := by decide
  have hdescent : baseEnd_6301577 < baseStart_6301577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301603 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4]
def baseStart_6301603 : Nat := 118140960795 + 6301603 * 2 ^ 59
def prefixEnd_6301603 : Nat := 4983230072969 + 3 ^ 40 * 6301603 * 2
def baseEnd_6301603 : Nat := 3235751232814613682981961

theorem tailTrace_6301603 : CollatzResearch.WordTrace tailWord_6301603 prefixEnd_6301603 3235751232814613682981961 := by
  unfold tailWord_6301603
  simp only [CollatzResearch.WordTrace]
  refine ⟨229838343389376033954613463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153225562259584022636408975 229838343389376033954613463)
  ·
    refine ⟨344757515084064050931920195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229838343389376033954613463 344757515084064050931920195)
    ·
      refine ⟨517136272626096076397880293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344757515084064050931920195 517136272626096076397880293)
      ·
        refine ⟨96963051117393014324602555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517136272626096076397880293 96963051117393014324602555)
        ·
          refine ⟨145444576676089521486903833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96963051117393014324602555 145444576676089521486903833)
          ·
            refine ⟨109083432507067141115177875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145444576676089521486903833 109083432507067141115177875)
            ·
              refine ⟨163625148760600711672766813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109083432507067141115177875 163625148760600711672766813)
              ·
                refine ⟨61359430785225266877287555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163625148760600711672766813 61359430785225266877287555)
                ·
                  refine ⟨92039146177837900315931333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 61359430785225266877287555 92039146177837900315931333)
                  ·
                    refine ⟨17257339908344606309237125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92039146177837900315931333 17257339908344606309237125)
                    ·
                      refine ⟨3235751232814613682981961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17257339908344606309237125 3235751232814613682981961)
                      ·
                        rfl

theorem cell23_6301603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_6301603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301603 prefixEnd_6301603 := by exact prefixLift 6301603
  have htrace : WordTrace (prefixWord ++ tailWord_6301603) baseStart_6301603 baseEnd_6301603 := by
    simpa [prefixWord, tailWord_6301603, baseEnd_6301603] using wordTrace_append hprefix tailTrace_6301603
  have hstable : (prefixWord ++ tailWord_6301603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301603).length < 2 ^ (prefixWord ++ tailWord_6301603).sum := by decide
  have hdescent : baseEnd_6301603 < baseStart_6301603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301628 : List Nat := [2, 2, 2, 5, 1, 1, 3, 1, 1, 3, 2]
def baseStart_6301628 : Nat := 118140960795 + 6301628 * 2 ^ 59
def prefixEnd_6301628 : Nat := 4983230072969 + 3 ^ 40 * 6301628 * 2
def baseEnd_6301628 : Nat := 3235764069830976085169347

theorem tailTrace_6301628 : CollatzResearch.WordTrace tailWord_6301628 prefixEnd_6301628 3235764069830976085169347 := by
  unfold tailWord_6301628
  simp only [CollatzResearch.WordTrace]
  refine ⟨114919627607142731612136769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153226170142856975482849025 114919627607142731612136769)
  ·
    refine ⟨86189720705357048709102577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114919627607142731612136769 86189720705357048709102577)
    ·
      refine ⟨64642290529017786531826933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86189720705357048709102577 64642290529017786531826933)
      ·
        refine ⟨6060214737095417487358775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64642290529017786531826933 6060214737095417487358775)
        ·
          refine ⟨9090322105643126231038163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6060214737095417487358775 9090322105643126231038163)
          ·
            refine ⟨13635483158464689346557245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090322105643126231038163 13635483158464689346557245)
            ·
              refine ⟨5113306184424258504958967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13635483158464689346557245 5113306184424258504958967)
              ·
                refine ⟨7669959276636387757438451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113306184424258504958967 7669959276636387757438451)
                ·
                  refine ⟨11504938914954581636157677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7669959276636387757438451 11504938914954581636157677)
                  ·
                    refine ⟨4314352093107968113559129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11504938914954581636157677 4314352093107968113559129)
                    ·
                      refine ⟨3235764069830976085169347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314352093107968113559129 3235764069830976085169347)
                      ·
                        rfl

theorem cell23_6301628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 3, 1, 1, 3, 2].length) (baseStart_6301628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301628 prefixEnd_6301628 := by exact prefixLift 6301628
  have htrace : WordTrace (prefixWord ++ tailWord_6301628) baseStart_6301628 baseEnd_6301628 := by
    simpa [prefixWord, tailWord_6301628, baseEnd_6301628] using wordTrace_append hprefix tailTrace_6301628
  have hstable : (prefixWord ++ tailWord_6301628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301628).length < 2 ^ (prefixWord ++ tailWord_6301628).sum := by decide
  have hdescent : baseEnd_6301628 < baseStart_6301628 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301654 : List Nat := [5, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4]
def baseStart_6301654 : Nat := 118140960795 + 6301654 * 2 ^ 59
def prefixEnd_6301654 : Nat := 4983230072969 + 3 ^ 40 * 6301654 * 2
def baseEnd_6301654 : Nat := 3235777420327992983444227

theorem tailTrace_6301654 : CollatzResearch.WordTrace tailWord_6301654 prefixEnd_6301654 3235777420327992983444227 := by
  unfold tailWord_6301654
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365012719511954354045001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153226802341460846443146677 14365012719511954354045001)
  ·
    refine ⟨10773759539633965765533751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14365012719511954354045001 10773759539633965765533751)
    ·
      refine ⟨16160639309450948648300627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10773759539633965765533751 16160639309450948648300627)
      ·
        refine ⟨24240958964176422972450941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16160639309450948648300627 24240958964176422972450941)
        ·
          refine ⟨9090359611566158614669103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24240958964176422972450941 9090359611566158614669103)
          ·
            refine ⟨13635539417349237922003655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090359611566158614669103 13635539417349237922003655)
            ·
              refine ⟨20453309126023856883005483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635539417349237922003655 20453309126023856883005483)
              ·
                refine ⟨30679963689035785324508225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20453309126023856883005483 30679963689035785324508225)
                ·
                  refine ⟨23009972766776838993381169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30679963689035785324508225 23009972766776838993381169)
                  ·
                    refine ⟨17257479575082629245035877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23009972766776838993381169 17257479575082629245035877)
                    ·
                      refine ⟨3235777420327992983444227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17257479575082629245035877 3235777420327992983444227)
                      ·
                        rfl

theorem cell23_6301654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4].length) (baseStart_6301654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301654 prefixEnd_6301654 := by exact prefixLift 6301654
  have htrace : WordTrace (prefixWord ++ tailWord_6301654) baseStart_6301654 baseEnd_6301654 := by
    simpa [prefixWord, tailWord_6301654, baseEnd_6301654] using wordTrace_append hprefix tailTrace_6301654
  have hstable : (prefixWord ++ tailWord_6301654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301654).length < 2 ^ (prefixWord ++ tailWord_6301654).sum := by decide
  have hdescent : baseEnd_6301654 < baseStart_6301654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301657 : List Nat := [1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 3]
def baseStart_6301657 : Nat := 118140960795 + 6301657 * 2 ^ 59
def prefixEnd_6301657 : Nat := 4983230072969 + 3 ^ 40 * 6301657 * 2
def baseEnd_6301657 : Nat := 3235778960769956471706713

theorem tailTrace_6301657 : CollatzResearch.WordTrace tailWord_6301657 prefixEnd_6301657 3235778960769956471706713 := by
  unfold tailWord_6301657
  simp only [CollatzResearch.WordTrace]
  refine ⟨229840312931180401177079225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153226875287453600784719483 229840312931180401177079225)
  ·
    refine ⟨172380234698385300882809419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229840312931180401177079225 172380234698385300882809419)
    ·
      refine ⟨258570352047577951324214129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172380234698385300882809419 258570352047577951324214129)
      ·
        refine ⟨193927764035683463493160597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258570352047577951324214129 193927764035683463493160597)
        ·
          refine ⟨9090363939172662351241903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 193927764035683463493160597 9090363939172662351241903)
          ·
            refine ⟨13635545908758993526862855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090363939172662351241903 13635545908758993526862855)
            ·
              refine ⟨20453318863138490290294283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635545908758993526862855 20453318863138490290294283)
              ·
                refine ⟨30679978294707735435441425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20453318863138490290294283 30679978294707735435441425)
                ·
                  refine ⟨23009983721030801576581069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30679978294707735435441425 23009983721030801576581069)
                  ·
                    refine ⟨8628743895386550591217901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23009983721030801576581069 8628743895386550591217901)
                    ·
                      refine ⟨3235778960769956471706713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8628743895386550591217901 3235778960769956471706713)
                      ·
                        rfl

theorem cell23_6301657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 3, 3].length) (baseStart_6301657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301657 prefixEnd_6301657 := by exact prefixLift 6301657
  have htrace : WordTrace (prefixWord ++ tailWord_6301657) baseStart_6301657 baseEnd_6301657 := by
    simpa [prefixWord, tailWord_6301657, baseEnd_6301657] using wordTrace_append hprefix tailTrace_6301657
  have hstable : (prefixWord ++ tailWord_6301657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301657).length < 2 ^ (prefixWord ++ tailWord_6301657).sum := by decide
  have hdescent : baseEnd_6301657 < baseStart_6301657 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301697 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 4, 4, 2]
def baseStart_6301697 : Nat := 118140960795 + 6301697 * 2 ^ 59
def prefixEnd_6301697 : Nat := 4983230072969 + 3 ^ 40 * 6301697 * 2
def baseEnd_6301697 : Nat := 3235799499996136315206529

theorem tailTrace_6301697 : CollatzResearch.WordTrace tailWord_6301697 prefixEnd_6301697 3235799499996136315206529 := by
  unfold tailWord_6301697
  simp only [CollatzResearch.WordTrace]
  refine ⟨229841771851035488008535345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153227847900690325339023563 229841771851035488008535345)
  ·
    refine ⟨172381328888276616006401509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229841771851035488008535345 172381328888276616006401509)
    ·
      refine ⟨32321499166551865501200283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172381328888276616006401509 32321499166551865501200283)
      ·
        refine ⟨48482248749827798251800425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32321499166551865501200283 48482248749827798251800425)
        ·
          refine ⟨36361686562370848688850319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48482248749827798251800425 36361686562370848688850319)
          ·
            refine ⟨54542529843556273033275479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36361686562370848688850319 54542529843556273033275479)
            ·
              refine ⟨81813794765334409549913219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54542529843556273033275479 81813794765334409549913219)
              ·
                refine ⟨122720692148001614324869829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81813794765334409549913219 122720692148001614324869829)
                ·
                  refine ⟨23010129777750302685913093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122720692148001614324869829 23010129777750302685913093)
                  ·
                    refine ⟨4314399333328181753608705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23010129777750302685913093 4314399333328181753608705)
                    ·
                      refine ⟨3235799499996136315206529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314399333328181753608705 3235799499996136315206529)
                      ·
                        rfl

theorem cell23_6301697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 4, 2].length) (baseStart_6301697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301697 prefixEnd_6301697 := by exact prefixLift 6301697
  have htrace : WordTrace (prefixWord ++ tailWord_6301697) baseStart_6301697 baseEnd_6301697 := by
    simpa [prefixWord, tailWord_6301697, baseEnd_6301697] using wordTrace_append hprefix tailTrace_6301697
  have hstable : (prefixWord ++ tailWord_6301697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301697).length < 2 ^ (prefixWord ++ tailWord_6301697).sum := by decide
  have hdescent : baseEnd_6301697 < baseStart_6301697 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301707 : List Nat := [1, 1, 1, 1, 6, 1, 4, 1, 3, 4]
def baseStart_6301707 : Nat := 118140960795 + 6301707 * 2 ^ 59
def prefixEnd_6301707 : Nat := 4983230072969 + 3 ^ 40 * 6301707 * 2
def baseEnd_6301707 : Nat := 1078601544934227092027161

theorem tailTrace_6301707 : CollatzResearch.WordTrace tailWord_6301707 prefixEnd_6301707 1078601544934227092027161 := by
  unfold tailWord_6301707
  simp only [CollatzResearch.WordTrace]
  refine ⟨229842136580999259716399375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153228091053999506477599583 229842136580999259716399375)
  ·
    refine ⟨344763204871498889574599063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229842136580999259716399375 344763204871498889574599063)
    ·
      refine ⟨517144807307248334361898595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344763204871498889574599063 517144807307248334361898595)
      ·
        refine ⟨775717210960872501542847893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517144807307248334361898595 775717210960872501542847893)
        ·
          refine ⟨36361744263790898509820995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 775717210960872501542847893 36361744263790898509820995)
          ·
            refine ⟨54542616395686347764731493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36361744263790898509820995 54542616395686347764731493)
            ·
              refine ⟨10226740574191190205887155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54542616395686347764731493 10226740574191190205887155)
              ·
                refine ⟨15340110861286785308830733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226740574191190205887155 15340110861286785308830733)
                ·
                  refine ⟨5752541572982544490811525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15340110861286785308830733 5752541572982544490811525)
                  ·
                    refine ⟨1078601544934227092027161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752541572982544490811525 1078601544934227092027161)
                    ·
                      rfl

theorem cell23_6301707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 4, 1, 3, 4].length) (baseStart_6301707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301707 prefixEnd_6301707 := by exact prefixLift 6301707
  have htrace : WordTrace (prefixWord ++ tailWord_6301707) baseStart_6301707 baseEnd_6301707 := by
    simpa [prefixWord, tailWord_6301707, baseEnd_6301707] using wordTrace_append hprefix tailTrace_6301707
  have hstable : (prefixWord ++ tailWord_6301707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301707).length < 2 ^ (prefixWord ++ tailWord_6301707).sum := by decide
  have hdescent : baseEnd_6301707 < baseStart_6301707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301710 : List Nat := [4, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6]
def baseStart_6301710 : Nat := 118140960795 + 6301710 * 2 ^ 59
def prefixEnd_6301710 : Nat := 4983230072969 + 3 ^ 40 * 6301710 * 2
def baseEnd_6301710 : Nat := 3235806175244644764343969

theorem tailTrace_6301710 : CollatzResearch.WordTrace tailWord_6301710 prefixEnd_6301710 3235806175244644764343969 := by
  unfold tailWord_6301710
  simp only [CollatzResearch.WordTrace]
  refine ⟨28730280749998548903594823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153228163999992260819172389 28730280749998548903594823)
  ·
    refine ⟨43095421124997823355392235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28730280749998548903594823 43095421124997823355392235)
    ·
      refine ⟨64643131687496735033088353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43095421124997823355392235 64643131687496735033088353)
      ·
        refine ⟨48482348765622551274816265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64643131687496735033088353 48482348765622551274816265)
        ·
          refine ⟨36361761574216913456112199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48482348765622551274816265 36361761574216913456112199)
          ·
            refine ⟨54542642361325370184168299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36361761574216913456112199 54542642361325370184168299)
            ·
              refine ⟨81813963541988055276252449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54542642361325370184168299 81813963541988055276252449)
              ·
                refine ⟨61360472656491041457189337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81813963541988055276252449 61360472656491041457189337)
                ·
                  refine ⟨46020354492368281092892003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61360472656491041457189337 46020354492368281092892003)
                  ·
                    refine ⟨69030531738552421639338005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46020354492368281092892003 69030531738552421639338005)
                    ·
                      refine ⟨3235806175244644764343969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69030531738552421639338005 3235806175244644764343969)
                      ·
                        rfl

theorem cell23_6301710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_6301710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301710 prefixEnd_6301710 := by exact prefixLift 6301710
  have htrace : WordTrace (prefixWord ++ tailWord_6301710) baseStart_6301710 baseEnd_6301710 := by
    simpa [prefixWord, tailWord_6301710, baseEnd_6301710] using wordTrace_append hprefix tailTrace_6301710
  have hstable : (prefixWord ++ tailWord_6301710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301710).length < 2 ^ (prefixWord ++ tailWord_6301710).sum := by decide
  have hdescent : baseEnd_6301710 < baseStart_6301710 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301747 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 3]
def baseStart_6301747 : Nat := 118140960795 + 6301747 * 2 ^ 59
def prefixEnd_6301747 : Nat := 4983230072969 + 3 ^ 40 * 6301747 * 2
def baseEnd_6301747 : Nat := 3235825174028861119581299

theorem tailTrace_6301747 : CollatzResearch.WordTrace tailWord_6301747 prefixEnd_6301747 3235825174028861119581299 := by
  unfold tailWord_6301747
  simp only [CollatzResearch.WordTrace]
  refine ⟨229843595500854346547855495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153229063667236231031903663 229843595500854346547855495)
  ·
    refine ⟨344765393251281519821783243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229843595500854346547855495 344765393251281519821783243)
    ·
      refine ⟨517148089876922279732674865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344765393251281519821783243 517148089876922279732674865)
      ·
        refine ⟨387861067407691709799506149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517148089876922279732674865 387861067407691709799506149)
        ·
          refine ⟨72723950138942195587407403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 387861067407691709799506149 72723950138942195587407403)
          ·
            refine ⟨109085925208413293381111105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72723950138942195587407403 109085925208413293381111105)
            ·
              refine ⟨81814443906309970035833329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109085925208413293381111105 81814443906309970035833329)
              ·
                refine ⟨61360832929732477526874997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81814443906309970035833329 61360832929732477526874997)
                ·
                  refine ⟨5752578087162419768144531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 61360832929732477526874997 5752578087162419768144531)
                  ·
                    refine ⟨8628867130743629652216797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5752578087162419768144531 8628867130743629652216797)
                    ·
                      refine ⟨3235825174028861119581299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8628867130743629652216797 3235825174028861119581299)
                      ·
                        rfl

theorem cell23_6301747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 5, 1, 3].length) (baseStart_6301747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301747 prefixEnd_6301747 := by exact prefixLift 6301747
  have htrace : WordTrace (prefixWord ++ tailWord_6301747) baseStart_6301747 baseEnd_6301747 := by
    simpa [prefixWord, tailWord_6301747, baseEnd_6301747] using wordTrace_append hprefix tailTrace_6301747
  have hstable : (prefixWord ++ tailWord_6301747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301747).length < 2 ^ (prefixWord ++ tailWord_6301747).sum := by decide
  have hdescent : baseEnd_6301747 < baseStart_6301747 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301758 : List Nat := [4, 2, 1, 3, 3, 1, 1, 1, 3, 4]
def baseStart_6301758 : Nat := 118140960795 + 6301758 * 2 ^ 59
def prefixEnd_6301758 : Nat := 4983230072969 + 3 ^ 40 * 6301758 * 2
def baseEnd_6301758 : Nat := 1078610274105353525514583

theorem tailTrace_6301758 : CollatzResearch.WordTrace tailWord_6301758 prefixEnd_6301758 1078610274105353525514583 := by
  unfold tailWord_6301758
  simp only [CollatzResearch.WordTrace]
  refine ⟨28730499587976811928313241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153229331135876330284337285 28730499587976811928313241)
  ·
    refine ⟨21547874690982608946234931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 28730499587976811928313241 21547874690982608946234931)
    ·
      refine ⟨32321812036473913419352397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21547874690982608946234931 32321812036473913419352397)
      ·
        refine ⟨12120679513677717532257149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32321812036473913419352397 12120679513677717532257149)
        ·
          refine ⟨4545254817629144074596431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12120679513677717532257149 4545254817629144074596431)
          ·
            refine ⟨6817882226443716111894647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4545254817629144074596431 6817882226443716111894647)
            ·
              refine ⟨10226823339665574167841971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817882226443716111894647 10226823339665574167841971)
              ·
                refine ⟨15340235009498361251762957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226823339665574167841971 15340235009498361251762957)
                ·
                  refine ⟨5752588128561885469411109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15340235009498361251762957 5752588128561885469411109)
                  ·
                    refine ⟨1078610274105353525514583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752588128561885469411109 1078610274105353525514583)
                    ·
                      rfl

theorem cell23_6301758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 3, 1, 1, 1, 3, 4].length) (baseStart_6301758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301758 prefixEnd_6301758 := by exact prefixLift 6301758
  have htrace : WordTrace (prefixWord ++ tailWord_6301758) baseStart_6301758 baseEnd_6301758 := by
    simpa [prefixWord, tailWord_6301758, baseEnd_6301758] using wordTrace_append hprefix tailTrace_6301758
  have hstable : (prefixWord ++ tailWord_6301758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301758).length < 2 ^ (prefixWord ++ tailWord_6301758).sum := by decide
  have hdescent : baseEnd_6301758 < baseStart_6301758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301770 : List Nat := [3, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4]
def baseStart_6301770 : Nat := 118140960795 + 6301770 * 2 ^ 59
def prefixEnd_6301770 : Nat := 4983230072969 + 3 ^ 40 * 6301770 * 2
def baseEnd_6301770 : Nat := 3235836984083914529593693

theorem tailTrace_6301770 : CollatzResearch.WordTrace tailWord_6301770 prefixEnd_6301770 3235836984083914529593693 := by
  unfold tailWord_6301770
  simp only [CollatzResearch.WordTrace]
  refine ⟨57461108594942755368985691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153229622919847347650628509 57461108594942755368985691)
  ·
    refine ⟨86191662892414133053478537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57461108594942755368985691 86191662892414133053478537)
    ·
      refine ⟨64643747169310599790108903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86191662892414133053478537 64643747169310599790108903)
      ·
        refine ⟨96965620753965899685163355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64643747169310599790108903 96965620753965899685163355)
        ·
          refine ⟨145448431130948849527745033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96965620753965899685163355 145448431130948849527745033)
          ·
            refine ⟨109086323348211637145808775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145448431130948849527745033 109086323348211637145808775)
            ·
              refine ⟨163629485022317455718713163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109086323348211637145808775 163629485022317455718713163)
              ·
                refine ⟨245444227533476183578069745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163629485022317455718713163 245444227533476183578069745)
                ·
                  refine ⟨184083170650107137683552309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245444227533476183578069745 184083170650107137683552309)
                  ·
                    refine ⟨17257797248447544157833029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 184083170650107137683552309 17257797248447544157833029)
                    ·
                      refine ⟨3235836984083914529593693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17257797248447544157833029 3235836984083914529593693)
                      ·
                        rfl

theorem cell23_6301770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_6301770 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301770 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301770 prefixEnd_6301770 := by exact prefixLift 6301770
  have htrace : WordTrace (prefixWord ++ tailWord_6301770) baseStart_6301770 baseEnd_6301770 := by
    simpa [prefixWord, tailWord_6301770, baseEnd_6301770] using wordTrace_append hprefix tailTrace_6301770
  have hstable : (prefixWord ++ tailWord_6301770).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301770).length < 2 ^ (prefixWord ++ tailWord_6301770).sum := by decide
  have hdescent : baseEnd_6301770 < baseStart_6301770 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301784 : List Nat := [2, 1, 2, 2, 1, 6, 1, 2, 1, 5]
def baseStart_6301784 : Nat := 118140960795 + 6301784 * 2 ^ 59
def prefixEnd_6301784 : Nat := 4983230072969 + 3 ^ 40 * 6301784 * 2
def baseEnd_6301784 : Nat := 1078614724271025824939543

theorem tailTrace_6301784 : CollatzResearch.WordTrace tailWord_6301784 prefixEnd_6301784 1078614724271025824939543 := by
  unfold tailWord_6301784
  simp only [CollatzResearch.WordTrace]
  refine ⟨114922472500860150933476203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153229963334480201244634937 114922472500860150933476203)
  ·
    refine ⟨172383708751290226400214305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114922472500860150933476203 172383708751290226400214305)
    ·
      refine ⟨129287781563467669800160729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172383708751290226400214305 129287781563467669800160729)
      ·
        refine ⟨96965836172600752350120547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129287781563467669800160729 96965836172600752350120547)
        ·
          refine ⟨145448754258901128525180821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96965836172600752350120547 145448754258901128525180821)
          ·
            refine ⟨6817910355885990399617851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 145448754258901128525180821 6817910355885990399617851)
            ·
              refine ⟨10226865533828985599426777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817910355885990399617851 10226865533828985599426777)
              ·
                refine ⟨7670149150371739199570083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10226865533828985599426777 7670149150371739199570083)
                ·
                  refine ⟨11505223725557608799355125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670149150371739199570083 11505223725557608799355125)
                  ·
                    refine ⟨1078614724271025824939543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11505223725557608799355125 1078614724271025824939543)
                    ·
                      rfl

theorem cell23_6301784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 6, 1, 2, 1, 5].length) (baseStart_6301784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301784 prefixEnd_6301784 := by exact prefixLift 6301784
  have htrace : WordTrace (prefixWord ++ tailWord_6301784) baseStart_6301784 baseEnd_6301784 := by
    simpa [prefixWord, tailWord_6301784, baseEnd_6301784] using wordTrace_append hprefix tailTrace_6301784
  have hstable : (prefixWord ++ tailWord_6301784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301784).length < 2 ^ (prefixWord ++ tailWord_6301784).sum := by decide
  have hdescent : baseEnd_6301784 < baseStart_6301784 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301797 : List Nat := [1, 3, 1, 3, 2, 3, 1, 2, 1, 6]
def baseStart_6301797 : Nat := 118140960795 + 6301797 * 2 ^ 59
def prefixEnd_6301797 : Nat := 4983230072969 + 3 ^ 40 * 6301797 * 2
def baseEnd_6301797 : Nat := 1078616949353861974652023

theorem tailTrace_6301797 : CollatzResearch.WordTrace tailWord_6301797 prefixEnd_6301797 1078616949353861974652023 := by
  unfold tailWord_6301797
  simp only [CollatzResearch.WordTrace]
  refine ⟨229845419150673205087175645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153230279433782136724783763 229845419150673205087175645)
  ·
    refine ⟨86192032181502451907690867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229845419150673205087175645 86192032181502451907690867)
    ·
      refine ⟨129288048272253677861536301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86192032181502451907690867 129288048272253677861536301)
      ·
        refine ⟨48483018102095129198076113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129288048272253677861536301 48483018102095129198076113)
        ·
          refine ⟨36362263576571346898557085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48483018102095129198076113 36362263576571346898557085)
          ·
            refine ⟨13635848841214255086958907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36362263576571346898557085 13635848841214255086958907)
            ·
              refine ⟨20453773261821382630438361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635848841214255086958907 20453773261821382630438361)
              ·
                refine ⟨15340329946366036972828771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20453773261821382630438361 15340329946366036972828771)
                ·
                  refine ⟨23010494919549055459243157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15340329946366036972828771 23010494919549055459243157)
                  ·
                    refine ⟨1078616949353861974652023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23010494919549055459243157 1078616949353861974652023)
                    ·
                      rfl

theorem cell23_6301797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 3, 1, 2, 1, 6].length) (baseStart_6301797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301797 prefixEnd_6301797 := by exact prefixLift 6301797
  have htrace : WordTrace (prefixWord ++ tailWord_6301797) baseStart_6301797 baseEnd_6301797 := by
    simpa [prefixWord, tailWord_6301797, baseEnd_6301797] using wordTrace_append hprefix tailTrace_6301797
  have hstable : (prefixWord ++ tailWord_6301797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301797).length < 2 ^ (prefixWord ++ tailWord_6301797).sum := by decide
  have hdescent : baseEnd_6301797 < baseStart_6301797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301807 : List Nat := [1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5]
def baseStart_6301807 : Nat := 118140960795 + 6301807 * 2 ^ 59
def prefixEnd_6301807 : Nat := 4983230072969 + 3 ^ 40 * 6301807 * 2
def baseEnd_6301807 : Nat := 3235855982868130884831023

theorem tailTrace_6301807 : CollatzResearch.WordTrace tailWord_6301807 prefixEnd_6301807 3235855982868130884831023 := by
  unfold tailWord_6301807
  simp only [CollatzResearch.WordTrace]
  refine ⟨229845783880636976795039675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153230522587091317863359783 229845783880636976795039675)
  ·
    refine ⟨344768675820955465192559513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229845783880636976795039675 344768675820955465192559513)
    ·
      refine ⟨258576506865716598894419635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344768675820955465192559513 258576506865716598894419635)
      ·
        refine ⟨387864760298574898341629453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258576506865716598894419635 387864760298574898341629453)
        ·
          refine ⟨145449285111965586878111045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387864760298574898341629453 145449285111965586878111045)
          ·
            refine ⟨27271740958493547539645821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145449285111965586878111045 27271740958493547539645821)
            ·
              refine ⟨10226902859435080327367183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27271740958493547539645821 10226902859435080327367183)
              ·
                refine ⟨15340354289152620491050775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226902859435080327367183 15340354289152620491050775)
                ·
                  refine ⟨23010531433728930736576163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15340354289152620491050775 23010531433728930736576163)
                  ·
                    refine ⟨34515797150593396104864245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23010531433728930736576163 34515797150593396104864245)
                    ·
                      refine ⟨3235855982868130884831023, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34515797150593396104864245 3235855982868130884831023)
                      ·
                        rfl

theorem cell23_6301807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 3, 1, 1, 1, 5].length) (baseStart_6301807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301807 prefixEnd_6301807 := by exact prefixLift 6301807
  have htrace : WordTrace (prefixWord ++ tailWord_6301807) baseStart_6301807 baseEnd_6301807 := by
    simpa [prefixWord, tailWord_6301807, baseEnd_6301807] using wordTrace_append hprefix tailTrace_6301807
  have hstable : (prefixWord ++ tailWord_6301807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301807).length < 2 ^ (prefixWord ++ tailWord_6301807).sum := by decide
  have hdescent : baseEnd_6301807 < baseStart_6301807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301810 : List Nat := [3, 2, 1, 2, 2, 13]
def baseStart_6301810 : Nat := 118140960795 + 6301810 * 2 ^ 59
def prefixEnd_6301810 : Nat := 4983230072969 + 3 ^ 40 * 6301810 * 2
def baseEnd_6301810 : Nat := 13316286104156766967463

theorem tailTrace_6301810 : CollatzResearch.WordTrace tailWord_6301810 prefixEnd_6301810 13316286104156766967463 := by
  unfold tailWord_6301810
  simp only [CollatzResearch.WordTrace]
  refine ⟨57461473324906527076849721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153230595533084072204932589 57461473324906527076849721)
  ·
    refine ⟨43096104993679895307637291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57461473324906527076849721 43096104993679895307637291)
    ·
      refine ⟨64644157490519842961455937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43096104993679895307637291 64644157490519842961455937)
      ·
        refine ⟨48483118117889882221091953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64644157490519842961455937 48483118117889882221091953)
        ·
          refine ⟨36362338588417411665818965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48483118117889882221091953 36362338588417411665818965)
          ·
            refine ⟨13316286104156766967463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 36362338588417411665818965 13316286104156766967463)
            ·
              rfl

theorem cell23_6301810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 13].length) (baseStart_6301810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301810 prefixEnd_6301810 := by exact prefixLift 6301810
  have htrace : WordTrace (prefixWord ++ tailWord_6301810) baseStart_6301810 baseEnd_6301810 := by
    simpa [prefixWord, tailWord_6301810, baseEnd_6301810] using wordTrace_append hprefix tailTrace_6301810
  have hstable : (prefixWord ++ tailWord_6301810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301810).length < 2 ^ (prefixWord ++ tailWord_6301810).sum := by decide
  have hdescent : baseEnd_6301810 < baseStart_6301810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301827 : List Nat := [1, 1, 1, 3, 3, 5, 1, 8]
def baseStart_6301827 : Nat := 118140960795 + 6301827 * 2 ^ 59
def prefixEnd_6301827 : Nat := 4983230072969 + 3 ^ 40 * 6301827 * 2
def baseEnd_6301827 : Nat := 119846898240045215058553

theorem tailTrace_6301827 : CollatzResearch.WordTrace tailWord_6301827 prefixEnd_6301827 119846898240045215058553 := by
  unfold tailWord_6301827
  simp only [CollatzResearch.WordTrace]
  refine ⟨229846513340564520210767735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153231008893709680140511823 229846513340564520210767735)
  ·
    refine ⟨344769770010846780316151603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229846513340564520210767735 344769770010846780316151603)
    ·
      refine ⟨517154655016270170474227405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344769770010846780316151603 517154655016270170474227405)
      ·
        refine ⟨193932995631101313927835277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517154655016270170474227405 193932995631101313927835277)
        ·
          refine ⟨72724873361662992722938229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193932995631101313927835277 72724873361662992722938229)
          ·
            refine ⟨6817956877655905567775459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72724873361662992722938229 6817956877655905567775459)
            ·
              refine ⟨10226935316483858351663189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6817956877655905567775459 10226935316483858351663189)
              ·
                refine ⟨119846898240045215058553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10226935316483858351663189 119846898240045215058553)
                ·
                  rfl

theorem cell23_6301827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 5, 1, 8].length) (baseStart_6301827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301827 prefixEnd_6301827 := by exact prefixLift 6301827
  have htrace : WordTrace (prefixWord ++ tailWord_6301827) baseStart_6301827 baseEnd_6301827 := by
    simpa [prefixWord, tailWord_6301827, baseEnd_6301827] using wordTrace_append hprefix tailTrace_6301827
  have hstable : (prefixWord ++ tailWord_6301827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301827).length < 2 ^ (prefixWord ++ tailWord_6301827).sum := by decide
  have hdescent : baseEnd_6301827 < baseStart_6301827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301834 : List Nat := [3, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4]
def baseStart_6301834 : Nat := 118140960795 + 6301834 * 2 ^ 59
def prefixEnd_6301834 : Nat := 4983230072969 + 3 ^ 40 * 6301834 * 2
def baseEnd_6301834 : Nat := 3235869846845802279193399

theorem tailTrace_6301834 : CollatzResearch.WordTrace tailWord_6301834 prefixEnd_6301834 3235869846845802279193399 := by
  unfold tailWord_6301834
  simp only [CollatzResearch.WordTrace]
  refine ⟨57461692162884790101568139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153231179101026106937515037 57461692162884790101568139)
  ·
    refine ⟨86192538244327185152352209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57461692162884790101568139 86192538244327185152352209)
    ·
      refine ⟨64644403683245388864264157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86192538244327185152352209 64644403683245388864264157)
      ·
        refine ⟨24241651381217020824099059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64644403683245388864264157 24241651381217020824099059)
        ·
          refine ⟨36362477071825531236148589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24241651381217020824099059 36362477071825531236148589)
          ·
            refine ⟨13635928901934574213555721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36362477071825531236148589 13635928901934574213555721)
            ·
              refine ⟨10226946676450930660166791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635928901934574213555721 10226946676450930660166791)
              ·
                refine ⟨15340420014676395990250187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10226946676450930660166791 15340420014676395990250187)
                ·
                  refine ⟨23010630022014593985375281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15340420014676395990250187 23010630022014593985375281)
                  ·
                    refine ⟨17257972516510945489031461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23010630022014593985375281 17257972516510945489031461)
                    ·
                      refine ⟨3235869846845802279193399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17257972516510945489031461 3235869846845802279193399)
                      ·
                        rfl

theorem cell23_6301834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_6301834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301834 prefixEnd_6301834 := by exact prefixLift 6301834
  have htrace : WordTrace (prefixWord ++ tailWord_6301834) baseStart_6301834 baseEnd_6301834 := by
    simpa [prefixWord, tailWord_6301834, baseEnd_6301834] using wordTrace_append hprefix tailTrace_6301834
  have hstable : (prefixWord ++ tailWord_6301834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301834).length < 2 ^ (prefixWord ++ tailWord_6301834).sum := by decide
  have hdescent : baseEnd_6301834 < baseStart_6301834 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301838 : List Nat := [4, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2]
def baseStart_6301838 : Nat := 118140960795 + 6301838 * 2 ^ 59
def prefixEnd_6301838 : Nat := 4983230072969 + 3 ^ 40 * 6301838 * 2
def baseEnd_6301838 : Nat := 3235871900768420263543381

theorem tailTrace_6301838 : CollatzResearch.WordTrace tailWord_6301838 prefixEnd_6301838 3235871900768420263543381 := by
  unfold tailWord_6301838
  simp only [CollatzResearch.WordTrace]
  refine ⟨28730864317940583636177271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153231276362349779392945445 28730864317940583636177271)
  ·
    refine ⟨43096296476910875454265907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28730864317940583636177271 43096296476910875454265907)
    ·
      refine ⟨64644444715366313181398861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43096296476910875454265907 64644444715366313181398861)
      ·
        refine ⟨24241666768262367443024573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64644444715366313181398861 24241666768262367443024573)
        ·
          refine ⟨9090625038098387791134215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24241666768262367443024573 9090625038098387791134215)
          ·
            refine ⟨13635937557147581686701323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9090625038098387791134215 13635937557147581686701323)
            ·
              refine ⟨20453906335721372530051985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13635937557147581686701323 20453906335721372530051985)
              ·
                refine ⟨15340429751791029397538989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20453906335721372530051985 15340429751791029397538989)
                ·
                  refine ⟨5752661156921636024077121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15340429751791029397538989 5752661156921636024077121)
                  ·
                    refine ⟨4314495867691227018057841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5752661156921636024077121 4314495867691227018057841)
                    ·
                      refine ⟨3235871900768420263543381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314495867691227018057841 3235871900768420263543381)
                      ·
                        rfl

theorem cell23_6301838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 2, 3, 2, 2].length) (baseStart_6301838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301838 prefixEnd_6301838 := by exact prefixLift 6301838
  have htrace : WordTrace (prefixWord ++ tailWord_6301838) baseStart_6301838 baseEnd_6301838 := by
    simpa [prefixWord, tailWord_6301838, baseEnd_6301838] using wordTrace_append hprefix tailTrace_6301838
  have hstable : (prefixWord ++ tailWord_6301838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301838).length < 2 ^ (prefixWord ++ tailWord_6301838).sum := by decide
  have hdescent : baseEnd_6301838 < baseStart_6301838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301840 : List Nat := [2, 1, 1, 1, 1, 1, 5, 2, 2, 7]
def baseStart_6301840 : Nat := 118140960795 + 6301840 * 2 ^ 59
def prefixEnd_6301840 : Nat := 4983230072969 + 3 ^ 40 * 6301840 * 2
def baseEnd_6301840 : Nat := 1078624309243243085239457

theorem tailTrace_6301840 : CollatzResearch.WordTrace tailWord_6301840 prefixEnd_6301840 1078624309243243085239457 := by
  unfold tailWord_6301840
  simp only [CollatzResearch.WordTrace]
  refine ⟨114923493744758711715495487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153231324993011615620660649 114923493744758711715495487)
  ·
    refine ⟨172385240617138067573243231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114923493744758711715495487 172385240617138067573243231)
    ·
      refine ⟨258577860925707101359864847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172385240617138067573243231 258577860925707101359864847)
      ·
        refine ⟨387866791388560652039797271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258577860925707101359864847 387866791388560652039797271)
        ·
          refine ⟨581800187082840978059695907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387866791388560652039797271 581800187082840978059695907)
          ·
            refine ⟨872700280624261467089543861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581800187082840978059695907 872700280624261467089543861)
            ·
              refine ⟨81815651308524512539644737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 872700280624261467089543861 81815651308524512539644737)
              ·
                refine ⟨61361738481393384404733553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81815651308524512539644737 61361738481393384404733553)
                ·
                  refine ⟨46021303861045038303550165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61361738481393384404733553 46021303861045038303550165)
                  ·
                    refine ⟨1078624309243243085239457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46021303861045038303550165 1078624309243243085239457)
                    ·
                      rfl

theorem cell23_6301840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 2, 2, 7].length) (baseStart_6301840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301840 prefixEnd_6301840 := by exact prefixLift 6301840
  have htrace : WordTrace (prefixWord ++ tailWord_6301840) baseStart_6301840 baseEnd_6301840 := by
    simpa [prefixWord, tailWord_6301840, baseEnd_6301840] using wordTrace_append hprefix tailTrace_6301840
  have hstable : (prefixWord ++ tailWord_6301840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301840).length < 2 ^ (prefixWord ++ tailWord_6301840).sum := by decide
  have hdescent : baseEnd_6301840 < baseStart_6301840 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301855 : List Nat := [1, 1, 2, 6, 1, 2, 2, 3, 1, 2, 2]
def baseStart_6301855 : Nat := 118140960795 + 6301855 * 2 ^ 59
def prefixEnd_6301855 : Nat := 4983230072969 + 3 ^ 40 * 6301855 * 2
def baseEnd_6301855 : Nat := 3235880629939546697030803

theorem tailTrace_6301855 : CollatzResearch.WordTrace tailWord_6301855 prefixEnd_6301855 3235880629939546697030803 := by
  unfold tailWord_6301855
  simp only [CollatzResearch.WordTrace]
  refine ⟨229847534584463080992787019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153231689722975387328524679 229847534584463080992787019)
  ·
    refine ⟨344771301876694621489180529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229847534584463080992787019 344771301876694621489180529)
    ·
      refine ⟨258578476407520966116885397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344771301876694621489180529 258578476407520966116885397)
      ·
        refine ⟨12120866081602545286729003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 258578476407520966116885397 12120866081602545286729003)
        ·
          refine ⟨18181299122403817930093505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12120866081602545286729003 18181299122403817930093505)
          ·
            refine ⟨13635974341802863447570129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18181299122403817930093505 13635974341802863447570129)
            ·
              refine ⟨10226980756352147585677597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13635974341802863447570129 10226980756352147585677597)
              ·
                refine ⟨3835117783632055344629099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10226980756352147585677597 3835117783632055344629099)
                ·
                  refine ⟨5752676675448083016943649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835117783632055344629099 5752676675448083016943649)
                  ·
                    refine ⟨4314507506586062262707737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5752676675448083016943649 4314507506586062262707737)
                    ·
                      refine ⟨3235880629939546697030803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314507506586062262707737 3235880629939546697030803)
                      ·
                        rfl

theorem cell23_6301855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_6301855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301855 prefixEnd_6301855 := by exact prefixLift 6301855
  have htrace : WordTrace (prefixWord ++ tailWord_6301855) baseStart_6301855 baseEnd_6301855 := by
    simpa [prefixWord, tailWord_6301855, baseEnd_6301855] using wordTrace_append hprefix tailTrace_6301855
  have hstable : (prefixWord ++ tailWord_6301855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301855).length < 2 ^ (prefixWord ++ tailWord_6301855).sum := by decide
  have hdescent : baseEnd_6301855 < baseStart_6301855 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301858 : List Nat := [3, 3, 1, 3, 1, 1, 4, 1, 1, 2, 3]
def baseStart_6301858 : Nat := 118140960795 + 6301858 * 2 ^ 59
def prefixEnd_6301858 : Nat := 4983230072969 + 3 ^ 40 * 6301858 * 2
def baseEnd_6301858 : Nat := 3235882170381510185293289

theorem tailTrace_6301858 : CollatzResearch.WordTrace tailWord_6301858 prefixEnd_6301858 3235882170381510185293289 := by
  unfold tailWord_6301858
  simp only [CollatzResearch.WordTrace]
  refine ⟨57461911000863053126286557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153231762668968141670097485 57461911000863053126286557)
  ·
    refine ⟨21548216625323644922357459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 57461911000863053126286557 21548216625323644922357459)
    ·
      refine ⟨32322324937985467383536189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21548216625323644922357459 32322324937985467383536189)
      ·
        refine ⟨12120871851744550268826071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32322324937985467383536189 12120871851744550268826071)
        ·
          refine ⟨18181307777616825403239107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12120871851744550268826071 18181307777616825403239107)
          ·
            refine ⟨27271961666425238104858661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18181307777616825403239107 27271961666425238104858661)
            ·
              refine ⟨5113492812454732144660999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27271961666425238104858661 5113492812454732144660999)
              ·
                refine ⟨7670239218682098216991499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113492812454732144660999 7670239218682098216991499)
                ·
                  refine ⟨11505358828023147325487249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670239218682098216991499 11505358828023147325487249)
                  ·
                    refine ⟨8629019121017360494115437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11505358828023147325487249 8629019121017360494115437)
                    ·
                      refine ⟨3235882170381510185293289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8629019121017360494115437 3235882170381510185293289)
                      ·
                        rfl

theorem cell23_6301858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_6301858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301858 prefixEnd_6301858 := by exact prefixLift 6301858
  have htrace : WordTrace (prefixWord ++ tailWord_6301858) baseStart_6301858 baseEnd_6301858 := by
    simpa [prefixWord, tailWord_6301858, baseEnd_6301858] using wordTrace_append hprefix tailTrace_6301858
  have hstable : (prefixWord ++ tailWord_6301858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301858).length < 2 ^ (prefixWord ++ tailWord_6301858).sum := by decide
  have hdescent : baseEnd_6301858 < baseStart_6301858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301888 : List Nat := [2, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3]
def baseStart_6301888 : Nat := 118140960795 + 6301888 * 2 ^ 59
def prefixEnd_6301888 : Nat := 4983230072969 + 3 ^ 40 * 6301888 * 2
def baseEnd_6301888 : Nat := 3235897574801145067918151

theorem tailTrace_6301888 : CollatzResearch.WordTrace tailWord_6301888 prefixEnd_6301888 3235897574801145067918151 := by
  unfold tailWord_6301888
  simp only [CollatzResearch.WordTrace]
  refine ⟨114924369096671763814369159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153232492128895685085825545 114924369096671763814369159)
  ·
    refine ⟨172386553645007645721553739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114924369096671763814369159 172386553645007645721553739)
    ·
      refine ⟨258579830467511468582330609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172386553645007645721553739 258579830467511468582330609)
      ·
        refine ⟨193934872850633601436747957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258579830467511468582330609 193934872850633601436747957)
        ·
          refine ⟨18181394329746900134695121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193934872850633601436747957 18181394329746900134695121)
          ·
            refine ⟨13636045747310175101021341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18181394329746900134695121 13636045747310175101021341)
            ·
              refine ⟨5113517155241315662883003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13636045747310175101021341 5113517155241315662883003)
              ·
                refine ⟨7670275732861973494324505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113517155241315662883003 7670275732861973494324505)
                ·
                  refine ⟨5752706799646480120743379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7670275732861973494324505 5752706799646480120743379)
                  ·
                    refine ⟨8629060199469720181115069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5752706799646480120743379 8629060199469720181115069)
                    ·
                      refine ⟨3235897574801145067918151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8629060199469720181115069 3235897574801145067918151)
                      ·
                        rfl

theorem cell23_6301888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 3, 1, 2, 1, 3].length) (baseStart_6301888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301888 prefixEnd_6301888 := by exact prefixLift 6301888
  have htrace : WordTrace (prefixWord ++ tailWord_6301888) baseStart_6301888 baseEnd_6301888 := by
    simpa [prefixWord, tailWord_6301888, baseEnd_6301888] using wordTrace_append hprefix tailTrace_6301888
  have hstable : (prefixWord ++ tailWord_6301888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301888).length < 2 ^ (prefixWord ++ tailWord_6301888).sum := by decide
  have hdescent : baseEnd_6301888 < baseStart_6301888 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301964 : List Nat := [2, 2, 1, 2, 2, 2, 4, 1, 2, 5]
def baseStart_6301964 : Nat := 118140960795 + 6301964 * 2 ^ 59
def prefixEnd_6301964 : Nat := 4983230072969 + 3 ^ 40 * 6301964 * 2
def baseEnd_6301964 : Nat := 1078645533110295590189267

theorem tailTrace_6301964 : CollatzResearch.WordTrace tailWord_6301964 prefixEnd_6301964 1078645533110295590189267 := by
  unfold tailWord_6301964
  simp only [CollatzResearch.WordTrace]
  refine ⟨114925755070534096304252473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153234340094045461739003297 114925755070534096304252473)
  ·
    refine ⟨86194316302900572228189355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114925755070534096304252473 86194316302900572228189355)
    ·
      refine ⟨129291474454350858342284033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86194316302900572228189355 129291474454350858342284033)
      ·
        refine ⟨96968605840763143756713025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129291474454350858342284033 96968605840763143756713025)
        ·
          refine ⟨72726454380572357817534769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96968605840763143756713025 72726454380572357817534769)
          ·
            refine ⟨54544840785429268363151077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72726454380572357817534769 54544840785429268363151077)
            ·
              refine ⟨10227157647267987818090827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54544840785429268363151077 10227157647267987818090827)
              ·
                refine ⟨15340736470901981727136241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10227157647267987818090827 15340736470901981727136241)
                ·
                  refine ⟨11505552353176486295352181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15340736470901981727136241 11505552353176486295352181)
                  ·
                    refine ⟨1078645533110295590189267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11505552353176486295352181 1078645533110295590189267)
                    ·
                      rfl

theorem cell23_6301964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 4, 1, 2, 5].length) (baseStart_6301964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301964 prefixEnd_6301964 := by exact prefixLift 6301964
  have htrace : WordTrace (prefixWord ++ tailWord_6301964) baseStart_6301964 baseEnd_6301964 := by
    simpa [prefixWord, tailWord_6301964, baseEnd_6301964] using wordTrace_append hprefix tailTrace_6301964
  have hstable : (prefixWord ++ tailWord_6301964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301964).length < 2 ^ (prefixWord ++ tailWord_6301964).sum := by decide
  have hdescent : baseEnd_6301964 < baseStart_6301964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301967 : List Nat := [1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4]
def baseStart_6301967 : Nat := 118140960795 + 6301967 * 2 ^ 59
def prefixEnd_6301967 : Nat := 4983230072969 + 3 ^ 40 * 6301967 * 2
def baseEnd_6301967 : Nat := 3235938139772850258830287

theorem tailTrace_6301967 : CollatzResearch.WordTrace tailWord_6301967 prefixEnd_6301967 3235938139772850258830287 := by
  unfold tailWord_6301967
  simp only [CollatzResearch.WordTrace]
  refine ⟨229851619560057324120864155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153234413040038216080576103 229851619560057324120864155)
  ·
    refine ⟨344777429340085986181296233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229851619560057324120864155 344777429340085986181296233)
    ·
      refine ⟨258583072005064489635972175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344777429340085986181296233 258583072005064489635972175)
      ·
        refine ⟨387874608007596734453958263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258583072005064489635972175 387874608007596734453958263)
        ·
          refine ⟨581811912011395101680937395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 387874608007596734453958263 581811912011395101680937395)
          ·
            refine ⟨872717868017092652521406093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 581811912011395101680937395 872717868017092652521406093)
            ·
              refine ⟨327269200506409744695527285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 872717868017092652521406093 327269200506409744695527285)
              ·
                refine ⟨30681487547475913565205683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 327269200506409744695527285 30681487547475913565205683)
                ·
                  refine ⟨46022231321213870347808525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30681487547475913565205683 46022231321213870347808525)
                  ·
                    refine ⟨17258336745455201380428197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46022231321213870347808525 17258336745455201380428197)
                    ·
                      refine ⟨3235938139772850258830287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17258336745455201380428197 3235938139772850258830287)
                      ·
                        rfl

theorem cell23_6301967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 5, 1, 3, 4].length) (baseStart_6301967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301967 prefixEnd_6301967 := by exact prefixLift 6301967
  have htrace : WordTrace (prefixWord ++ tailWord_6301967) baseStart_6301967 baseEnd_6301967 := by
    simpa [prefixWord, tailWord_6301967, baseEnd_6301967] using wordTrace_append hprefix tailTrace_6301967
  have hstable : (prefixWord ++ tailWord_6301967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301967).length < 2 ^ (prefixWord ++ tailWord_6301967).sum := by decide
  have hdescent : baseEnd_6301967 < baseStart_6301967 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6301987 : List Nat := [1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5]
def baseStart_6301987 : Nat := 118140960795 + 6301987 * 2 ^ 59
def prefixEnd_6301987 : Nat := 4983230072969 + 3 ^ 40 * 6301987 * 2
def baseEnd_6301987 : Nat := 3235948409385940180580195

theorem tailTrace_6301987 : CollatzResearch.WordTrace tailWord_6301987 prefixEnd_6301987 3235948409385940180580195 := by
  unfold tailWord_6301987
  simp only [CollatzResearch.WordTrace]
  refine ⟨229852349019984867536592215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153234899346656578357728143 229852349019984867536592215)
  ·
    refine ⟨344778523529977301304888323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229852349019984867536592215 344778523529977301304888323)
    ·
      refine ⟨517167785294965951957332485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344778523529977301304888323 517167785294965951957332485)
      ·
        refine ⟨96968959742806115991999841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517167785294965951957332485 96968959742806115991999841)
        ·
          refine ⟨72726719807104586993999881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96968959742806115991999841 72726719807104586993999881)
          ·
            refine ⟨54545039855328440245499911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72726719807104586993999881 54545039855328440245499911)
            ·
              refine ⟨81817559782992660368249867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54545039855328440245499911 81817559782992660368249867)
              ·
                refine ⟨122726339674488990552374801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81817559782992660368249867 122726339674488990552374801)
                ·
                  refine ⟨92044754755866742914281101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122726339674488990552374801 92044754755866742914281101)
                  ·
                    refine ⟨34516783033450028592855413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 92044754755866742914281101 34516783033450028592855413)
                    ·
                      refine ⟨3235948409385940180580195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34516783033450028592855413 3235948409385940180580195)
                      ·
                        rfl

theorem cell23_6301987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_6301987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6301987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6301987 prefixEnd_6301987 := by exact prefixLift 6301987
  have htrace : WordTrace (prefixWord ++ tailWord_6301987) baseStart_6301987 baseEnd_6301987 := by
    simpa [prefixWord, tailWord_6301987, baseEnd_6301987] using wordTrace_append hprefix tailTrace_6301987
  have hstable : (prefixWord ++ tailWord_6301987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6301987).length < 2 ^ (prefixWord ++ tailWord_6301987).sum := by decide
  have hdescent : baseEnd_6301987 < baseStart_6301987 := by decide
  rcases family_descends (prefixWord ++ tailWord_6301987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302028 : List Nat := [2, 2, 1, 3, 2, 1, 4, 3, 1, 4]
def baseStart_6302028 : Nat := 118140960795 + 6302028 * 2 ^ 59
def prefixEnd_6302028 : Nat := 4983230072969 + 3 ^ 40 * 6302028 * 2
def baseEnd_6302028 : Nat := 1078656487364258173389169

theorem tailTrace_6302028 : CollatzResearch.WordTrace tailWord_6302028 prefixEnd_6302028 1078656487364258173389169 := by
  unfold tailWord_6302028
  simp only [CollatzResearch.WordTrace]
  refine ⟨114926922206418165769417369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153235896275224221025889825 114926922206418165769417369)
  ·
    refine ⟨86195191654813624327063027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114926922206418165769417369 86195191654813624327063027)
    ·
      refine ⟨129292787482220436490594541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86195191654813624327063027 129292787482220436490594541)
      ·
        refine ⟨48484795305832663683972953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129292787482220436490594541 48484795305832663683972953)
        ·
          refine ⟨36363596479374497762979715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48484795305832663683972953 36363596479374497762979715)
          ·
            refine ⟨54545394719061746644469573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36363596479374497762979715 54545394719061746644469573)
            ·
              refine ⟨10227261509824077495838045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54545394719061746644469573 10227261509824077495838045)
              ·
                refine ⟨3835223066184029060939267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10227261509824077495838045 3835223066184029060939267)
                ·
                  refine ⟨5752834599276043591408901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835223066184029060939267 5752834599276043591408901)
                  ·
                    refine ⟨1078656487364258173389169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752834599276043591408901 1078656487364258173389169)
                    ·
                      rfl

theorem cell23_6302028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 4, 3, 1, 4].length) (baseStart_6302028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302028 prefixEnd_6302028 := by exact prefixLift 6302028
  have htrace : WordTrace (prefixWord ++ tailWord_6302028) baseStart_6302028 baseEnd_6302028 := by
    simpa [prefixWord, tailWord_6302028, baseEnd_6302028] using wordTrace_append hprefix tailTrace_6302028
  have hstable : (prefixWord ++ tailWord_6302028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302028).length < 2 ^ (prefixWord ++ tailWord_6302028).sum := by decide
  have hdescent : baseEnd_6302028 < baseStart_6302028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302058 : List Nat := [3, 1, 3, 3, 1, 2, 3, 1, 6]
def baseStart_6302058 : Nat := 118140960795 + 6302058 * 2 ^ 59
def prefixEnd_6302058 : Nat := 4983230072969 + 3 ^ 40 * 6302058 * 2
def baseEnd_6302058 : Nat := 359553874056934378088041

theorem tailTrace_6302058 : CollatzResearch.WordTrace tailWord_6302058 prefixEnd_6302058 359553874056934378088041 := by
  unfold tailWord_6302058
  simp only [CollatzResearch.WordTrace]
  refine ⟨57463734650681911665606707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153236625735151764441617885 57463734650681911665606707)
  ·
    refine ⟨86195601976022867498410061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57463734650681911665606707 86195601976022867498410061)
    ·
      refine ⟨32323350741008575311903773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86195601976022867498410061 32323350741008575311903773)
      ·
        refine ⟨12121256527878215741963915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32323350741008575311903773 12121256527878215741963915)
        ·
          refine ⟨18181884791817323612945873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12121256527878215741963915 18181884791817323612945873)
          ·
            refine ⟨13636413593862992709709405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18181884791817323612945873 13636413593862992709709405)
            ·
              refine ⟨5113655097698622266141027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13636413593862992709709405 5113655097698622266141027)
              ·
                refine ⟨7670482646547933399211541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5113655097698622266141027 7670482646547933399211541)
                ·
                  refine ⟨359553874056934378088041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7670482646547933399211541 359553874056934378088041)
                  ·
                    rfl

theorem cell23_6302058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 1, 6].length) (baseStart_6302058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302058 prefixEnd_6302058 := by exact prefixLift 6302058
  have htrace : WordTrace (prefixWord ++ tailWord_6302058) baseStart_6302058 baseEnd_6302058 := by
    simpa [prefixWord, tailWord_6302058, baseEnd_6302058] using wordTrace_append hprefix tailTrace_6302058
  have hstable : (prefixWord ++ tailWord_6302058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302058).length < 2 ^ (prefixWord ++ tailWord_6302058).sum := by decide
  have hdescent : baseEnd_6302058 < baseStart_6302058 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302061 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 3, 5, 2]
def baseStart_6302061 : Nat := 118140960795 + 6302061 * 2 ^ 59
def prefixEnd_6302061 : Nat := 4983230072969 + 3 ^ 40 * 6302061 * 2
def baseEnd_6302061 : Nat := 3235986406954372891054855

theorem tailTrace_6302061 : CollatzResearch.WordTrace tailWord_6302061 prefixEnd_6302061 3235986406954372891054855 := by
  unfold tailWord_6302061
  simp only [CollatzResearch.WordTrace]
  refine ⟨229855048021716778174786037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153236698681144518783190691 229855048021716778174786037)
  ·
    refine ⟨21548910752035947953886191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229855048021716778174786037 21548910752035947953886191)
    ·
      refine ⟨32323366128053921930829287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21548910752035947953886191 32323366128053921930829287)
      ·
        refine ⟨48485049192080882896243931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32323366128053921930829287 48485049192080882896243931)
        ·
          refine ⟨72727573788121324344365897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48485049192080882896243931 72727573788121324344365897)
          ·
            refine ⟨54545680341090993258274423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72727573788121324344365897 54545680341090993258274423)
            ·
              refine ⟨81818520511636489887411635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54545680341090993258274423 81818520511636489887411635)
              ·
                refine ⟨122727780767454734831117453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81818520511636489887411635 122727780767454734831117453)
                ·
                  refine ⟨46022917787795525561669045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 122727780767454734831117453 46022917787795525561669045)
                  ·
                    refine ⟨4314648542605830521406473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46022917787795525561669045 4314648542605830521406473)
                    ·
                      refine ⟨3235986406954372891054855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314648542605830521406473 3235986406954372891054855)
                      ·
                        rfl

theorem cell23_6302061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 3, 5, 2].length) (baseStart_6302061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302061 prefixEnd_6302061 := by exact prefixLift 6302061
  have htrace : WordTrace (prefixWord ++ tailWord_6302061) baseStart_6302061 baseEnd_6302061 := by
    simpa [prefixWord, tailWord_6302061, baseEnd_6302061] using wordTrace_append hprefix tailTrace_6302061
  have hstable : (prefixWord ++ tailWord_6302061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302061).length < 2 ^ (prefixWord ++ tailWord_6302061).sum := by decide
  have hdescent : baseEnd_6302061 < baseStart_6302061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302084 : List Nat := [2, 3, 2, 1, 1, 2, 2, 1, 3, 6]
def baseStart_6302084 : Nat := 118140960795 + 6302084 * 2 ^ 59
def prefixEnd_6302084 : Nat := 4983230072969 + 3 ^ 40 * 6302084 * 2
def baseEnd_6302084 : Nat := 1078666072336475433689083

theorem tailTrace_6302084 : CollatzResearch.WordTrace tailWord_6302084 prefixEnd_6302084 1078666072336475433689083 := by
  unfold tailWord_6302084
  simp only [CollatzResearch.WordTrace]
  refine ⟨114927943450316726551436653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153237257933755635401915537 114927943450316726551436653)
  ·
    refine ⟨43097978793868772456788745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 114927943450316726551436653 43097978793868772456788745)
    ·
      refine ⟨32323484095401579342591559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43097978793868772456788745 32323484095401579342591559)
      ·
        refine ⟨48485226143102369013887339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32323484095401579342591559 48485226143102369013887339)
        ·
          refine ⟨72727839214653553520831009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48485226143102369013887339 72727839214653553520831009)
          ·
            refine ⟨54545879410990165140623257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72727839214653553520831009 54545879410990165140623257)
            ·
              refine ⟨40909409558242623855467443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54545879410990165140623257 40909409558242623855467443)
              ·
                refine ⟨61364114337363935783201165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40909409558242623855467443 61364114337363935783201165)
                ·
                  refine ⟨23011542876511475918700437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61364114337363935783201165 23011542876511475918700437)
                  ·
                    refine ⟨1078666072336475433689083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23011542876511475918700437 1078666072336475433689083)
                    ·
                      rfl

theorem cell23_6302084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 2, 2, 1, 3, 6].length) (baseStart_6302084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302084 prefixEnd_6302084 := by exact prefixLift 6302084
  have htrace : WordTrace (prefixWord ++ tailWord_6302084) baseStart_6302084 baseEnd_6302084 := by
    simpa [prefixWord, tailWord_6302084, baseEnd_6302084] using wordTrace_append hprefix tailTrace_6302084
  have hstable : (prefixWord ++ tailWord_6302084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302084).length < 2 ^ (prefixWord ++ tailWord_6302084).sum := by decide
  have hdescent : baseEnd_6302084 < baseStart_6302084 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302091 : List Nat := [1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 4]
def baseStart_6302091 : Nat := 118140960795 + 6302091 * 2 ^ 59
def prefixEnd_6302091 : Nat := 4983230072969 + 3 ^ 40 * 6302091 * 2
def baseEnd_6302091 : Nat := 3236001811374007773679717

theorem tailTrace_6302091 : CollatzResearch.WordTrace tailWord_6302091 prefixEnd_6302091 3236001811374007773679717 := by
  unfold tailWord_6302091
  simp only [CollatzResearch.WordTrace]
  refine ⟨229856142211608093298378127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153237428141072062198918751 229856142211608093298378127)
  ·
    refine ⟨344784213317412139947567191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229856142211608093298378127 344784213317412139947567191)
    ·
      refine ⟨517176319976118209921350787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344784213317412139947567191 517176319976118209921350787)
      ·
        refine ⟨775764479964177314882026181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517176319976118209921350787 775764479964177314882026181)
        ·
          refine ⟨145455839993283246540379909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 775764479964177314882026181 145455839993283246540379909)
          ·
            refine ⟨27272969998740608726321233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145455839993283246540379909 27272969998740608726321233)
            ·
              refine ⟨20454727499055456544740925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27272969998740608726321233 20454727499055456544740925)
              ·
                refine ⟨7670522812145796204277847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20454727499055456544740925 7670522812145796204277847)
                ·
                  refine ⟨11505784218218694306416771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670522812145796204277847 11505784218218694306416771)
                  ·
                    refine ⟨17258676327328041459625157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11505784218218694306416771 17258676327328041459625157)
                    ·
                      refine ⟨3236001811374007773679717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17258676327328041459625157 3236001811374007773679717)
                      ·
                        rfl

theorem cell23_6302091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 2, 3, 1, 1, 4].length) (baseStart_6302091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302091 prefixEnd_6302091 := by exact prefixLift 6302091
  have htrace : WordTrace (prefixWord ++ tailWord_6302091) baseStart_6302091 baseEnd_6302091 := by
    simpa [prefixWord, tailWord_6302091, baseEnd_6302091] using wordTrace_append hprefix tailTrace_6302091
  have hstable : (prefixWord ++ tailWord_6302091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302091).length < 2 ^ (prefixWord ++ tailWord_6302091).sum := by decide
  have hdescent : baseEnd_6302091 < baseStart_6302091 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302101 : List Nat := [1, 3, 2, 1, 1, 2, 1, 6, 2, 4]
def baseStart_6302101 : Nat := 118140960795 + 6302101 * 2 ^ 59
def prefixEnd_6302101 : Nat := 4983230072969 + 3 ^ 40 * 6302101 * 2
def baseEnd_6302101 : Nat := 1078668982060184244851557

theorem tailTrace_6302101 : CollatzResearch.WordTrace tailWord_6302101 prefixEnd_6302101 1078668982060184244851557 := by
  unfold tailWord_6302101
  simp only [CollatzResearch.WordTrace]
  refine ⟨229856506941571865006242157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153237671294381243337494771 229856506941571865006242157)
  ·
    refine ⟨86196190103089449377340809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229856506941571865006242157 86196190103089449377340809)
    ·
      refine ⟨64647142577317087033005607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86196190103089449377340809 64647142577317087033005607)
      ·
        refine ⟨96970713865975630549508411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64647142577317087033005607 96970713865975630549508411)
        ·
          refine ⟨145456070798963445824262617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96970713865975630549508411 145456070798963445824262617)
          ·
            refine ⟨109092053099222584368196963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145456070798963445824262617 109092053099222584368196963)
            ·
              refine ⟨163638079648833876552295445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109092053099222584368196963 163638079648833876552295445)
              ·
                refine ⟨7670534983539087963388849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 163638079648833876552295445 7670534983539087963388849)
                ·
                  refine ⟨5752901237654315972541637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7670534983539087963388849 5752901237654315972541637)
                  ·
                    refine ⟨1078668982060184244851557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5752901237654315972541637 1078668982060184244851557)
                    ·
                      rfl

theorem cell23_6302101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 6, 2, 4].length) (baseStart_6302101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302101 prefixEnd_6302101 := by exact prefixLift 6302101
  have htrace : WordTrace (prefixWord ++ tailWord_6302101) baseStart_6302101 baseEnd_6302101 := by
    simpa [prefixWord, tailWord_6302101, baseEnd_6302101] using wordTrace_append hprefix tailTrace_6302101
  have hstable : (prefixWord ++ tailWord_6302101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302101).length < 2 ^ (prefixWord ++ tailWord_6302101).sum := by decide
  have hdescent : baseEnd_6302101 < baseStart_6302101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302111 : List Nat := [1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3]
def baseStart_6302111 : Nat := 118140960795 + 6302111 * 2 ^ 59
def prefixEnd_6302111 : Nat := 4983230072969 + 3 ^ 40 * 6302111 * 2
def baseEnd_6302111 : Nat := 3236012080987097695429625

theorem tailTrace_6302111 : CollatzResearch.WordTrace tailWord_6302111 prefixEnd_6302111 3236012080987097695429625 := by
  unfold tailWord_6302111
  simp only [CollatzResearch.WordTrace]
  refine ⟨229856871671535636714106187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153237914447690424476070791 229856871671535636714106187)
  ·
    refine ⟨344785307507303455071159281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229856871671535636714106187 344785307507303455071159281)
    ·
      refine ⟨258588980630477591303369461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344785307507303455071159281 258588980630477591303369461)
      ·
        refine ⟨24242716934107274184690887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 258588980630477591303369461 24242716934107274184690887)
        ·
          refine ⟨36364075401160911277036331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24242716934107274184690887 36364075401160911277036331)
          ·
            refine ⟨54546113101741366915554497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36364075401160911277036331 54546113101741366915554497)
            ·
              refine ⟨40909584826306025186665873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54546113101741366915554497 40909584826306025186665873)
              ·
                refine ⟨30682188619729518889999405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40909584826306025186665873 30682188619729518889999405)
                ·
                  refine ⟨11505820732398569583749777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30682188619729518889999405 11505820732398569583749777)
                  ·
                    refine ⟨8629365549298927187812333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11505820732398569583749777 8629365549298927187812333)
                    ·
                      refine ⟨3236012080987097695429625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8629365549298927187812333 3236012080987097695429625)
                      ·
                        rfl

theorem cell23_6302111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_6302111 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302111 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302111 prefixEnd_6302111 := by exact prefixLift 6302111
  have htrace : WordTrace (prefixWord ++ tailWord_6302111) baseStart_6302111 baseEnd_6302111 := by
    simpa [prefixWord, tailWord_6302111, baseEnd_6302111] using wordTrace_append hprefix tailTrace_6302111
  have hstable : (prefixWord ++ tailWord_6302111).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302111).length < 2 ^ (prefixWord ++ tailWord_6302111).sum := by decide
  have hdescent : baseEnd_6302111 < baseStart_6302111 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302141 : List Nat := [1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 3]
def baseStart_6302141 : Nat := 118140960795 + 6302141 * 2 ^ 59
def prefixEnd_6302141 : Nat := 4983230072969 + 3 ^ 40 * 6302141 * 2
def baseEnd_6302141 : Nat := 3236027485406732578054487

theorem tailTrace_6302141 : CollatzResearch.WordTrace tailWord_6302141 prefixEnd_6302141 3236027485406732578054487 := by
  unfold tailWord_6302141
  simp only [CollatzResearch.WordTrace]
  refine ⟨229857965861426951837698277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153238643907617967891798851 229857965861426951837698277)
  ·
    refine ⟨43098368599017553469568427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229857965861426951837698277 43098368599017553469568427)
    ·
      refine ⟨64647552898526330204352641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43098368599017553469568427 64647552898526330204352641)
      ·
        refine ⟨48485664673894747653264481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64647552898526330204352641 48485664673894747653264481)
        ·
          refine ⟨36364248505421060739948361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48485664673894747653264481 36364248505421060739948361)
          ·
            refine ⟨27273186379065795554961271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36364248505421060739948361 27273186379065795554961271)
            ·
              refine ⟨40909779568598693332441907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27273186379065795554961271 40909779568598693332441907)
              ·
                refine ⟨61364669352898039998662861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40909779568598693332441907 61364669352898039998662861)
                ·
                  refine ⟨23011751007336764999498573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61364669352898039998662861 23011751007336764999498573)
                  ·
                    refine ⟨8629406627751286874811965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23011751007336764999498573 8629406627751286874811965)
                    ·
                      refine ⟨3236027485406732578054487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8629406627751286874811965 3236027485406732578054487)
                      ·
                        rfl

theorem cell23_6302141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_6302141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302141 prefixEnd_6302141 := by exact prefixLift 6302141
  have htrace : WordTrace (prefixWord ++ tailWord_6302141) baseStart_6302141 baseEnd_6302141 := by
    simpa [prefixWord, tailWord_6302141, baseEnd_6302141] using wordTrace_append hprefix tailTrace_6302141
  have hstable : (prefixWord ++ tailWord_6302141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302141).length < 2 ^ (prefixWord ++ tailWord_6302141).sum := by decide
  have hdescent : baseEnd_6302141 < baseStart_6302141 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302204 : List Nat := [2, 2, 2, 1, 2, 1, 1, 1, 11]
def baseStart_6302204 : Nat := 118140960795 + 6302204 * 2 ^ 59
def prefixEnd_6302204 : Nat := 4983230072969 + 3 ^ 40 * 6302204 * 2
def baseEnd_6302204 : Nat := 359562203854218425729633

theorem tailTrace_6302204 : CollatzResearch.WordTrace tailWord_6302204 prefixEnd_6302204 359562203854218425729633 := by
  unfold tailWord_6302204
  simp only [CollatzResearch.WordTrace]
  refine ⟨114930131830099356798620833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153240175773465809064827777 114930131830099356798620833)
  ·
    refine ⟨86197598872574517598965625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114930131830099356798620833 86197598872574517598965625)
    ·
      refine ⟨64648199154430888199224219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86197598872574517598965625 64648199154430888199224219)
      ·
        refine ⟨96972298731646332298836329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64648199154430888199224219 96972298731646332298836329)
        ·
          refine ⟨72729224048734749224127247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96972298731646332298836329 72729224048734749224127247)
          ·
            refine ⟨109093836073102123836190871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72729224048734749224127247 109093836073102123836190871)
            ·
              refine ⟨163640754109653185754286307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109093836073102123836190871 163640754109653185754286307)
              ·
                refine ⟨245461131164479778631429461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 163640754109653185754286307 245461131164479778631429461)
                ·
                  refine ⟨359562203854218425729633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 245461131164479778631429461 359562203854218425729633)
                  ·
                    rfl

theorem cell23_6302204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 1, 11].length) (baseStart_6302204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302204 prefixEnd_6302204 := by exact prefixLift 6302204
  have htrace : WordTrace (prefixWord ++ tailWord_6302204) baseStart_6302204 baseEnd_6302204 := by
    simpa [prefixWord, tailWord_6302204, baseEnd_6302204] using wordTrace_append hprefix tailTrace_6302204
  have hstable : (prefixWord ++ tailWord_6302204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302204).length < 2 ^ (prefixWord ++ tailWord_6302204).sum := by decide
  have hdescent : baseEnd_6302204 < baseStart_6302204 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302261 : List Nat := [1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 5]
def baseStart_6302261 : Nat := 118140960795 + 6302261 * 2 ^ 59
def prefixEnd_6302261 : Nat := 4983230072969 + 3 ^ 40 * 6302261 * 2
def baseEnd_6302261 : Nat := 3236089103085272108553935

theorem tailTrace_6302261 : CollatzResearch.WordTrace tailWord_6302261 prefixEnd_6302261 3236089103085272108553935 := by
  unfold tailWord_6302261
  simp only [CollatzResearch.WordTrace]
  refine ⟨229862342620992212332066637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153241561747328141554711091 229862342620992212332066637)
  ·
    refine ⟨86198378482872079624524989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229862342620992212332066637 86198378482872079624524989)
    ·
      refine ⟨32324391931077029859196871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86198378482872079624524989 32324391931077029859196871)
      ·
        refine ⟨48486587896615544788795307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32324391931077029859196871 48486587896615544788795307)
        ·
          refine ⟨72729881844923317183192961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48486587896615544788795307 72729881844923317183192961)
          ·
            refine ⟨54547411383692487887394721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72729881844923317183192961 54547411383692487887394721)
            ·
              refine ⟨40910558537769365915546041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54547411383692487887394721 40910558537769365915546041)
              ·
                refine ⟨30682918903327024436659531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40910558537769365915546041 30682918903327024436659531)
                ·
                  refine ⟨46024378354990536654989297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30682918903327024436659531 46024378354990536654989297)
                  ·
                    refine ⟨34518283766242902491241973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 46024378354990536654989297 34518283766242902491241973)
                    ·
                      refine ⟨3236089103085272108553935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34518283766242902491241973 3236089103085272108553935)
                      ·
                        rfl

theorem cell23_6302261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 2, 1, 2, 5].length) (baseStart_6302261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302261 prefixEnd_6302261 := by exact prefixLift 6302261
  have htrace : WordTrace (prefixWord ++ tailWord_6302261) baseStart_6302261 baseEnd_6302261 := by
    simpa [prefixWord, tailWord_6302261, baseEnd_6302261] using wordTrace_append hprefix tailTrace_6302261
  have hstable : (prefixWord ++ tailWord_6302261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302261).length < 2 ^ (prefixWord ++ tailWord_6302261).sum := by decide
  have hdescent : baseEnd_6302261 < baseStart_6302261 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302268 : List Nat := [2, 2, 2, 2, 3, 2, 1, 2, 2, 5]
def baseStart_6302268 : Nat := 118140960795 + 6302268 * 2 ^ 59
def prefixEnd_6302268 : Nat := 4983230072969 + 3 ^ 40 * 6302268 * 2
def baseEnd_6302268 : Nat := 1078697565816617860388801

theorem tailTrace_6302268 : CollatzResearch.WordTrace tailWord_6302268 prefixEnd_6302268 1078697565816617860388801 := by
  unfold tailWord_6302268
  simp only [CollatzResearch.WordTrace]
  refine ⟨114931298965983426263785729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153241731954644568351714305 114931298965983426263785729)
  ·
    refine ⟨86198474224487569697839297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114931298965983426263785729 86198474224487569697839297)
    ·
      refine ⟨64648855668365677273379473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86198474224487569697839297 64648855668365677273379473)
      ·
        refine ⟨48486641751274257955034605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64648855668365677273379473 48486641751274257955034605)
        ·
          refine ⟨18182490656727846733137977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48486641751274257955034605 18182490656727846733137977)
          ·
            refine ⟨13636867992545885049853483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18182490656727846733137977 13636867992545885049853483)
            ·
              refine ⟨20455301988818827574780225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13636867992545885049853483 20455301988818827574780225)
              ·
                refine ⟨15341476491614120681085169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20455301988818827574780225 15341476491614120681085169)
                ·
                  refine ⟨11506107368710590510813877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15341476491614120681085169 11506107368710590510813877)
                  ·
                    refine ⟨1078697565816617860388801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11506107368710590510813877 1078697565816617860388801)
                    ·
                      rfl

theorem cell23_6302268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 1, 2, 2, 5].length) (baseStart_6302268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302268 prefixEnd_6302268 := by exact prefixLift 6302268
  have htrace : WordTrace (prefixWord ++ tailWord_6302268) baseStart_6302268 baseEnd_6302268 := by
    simpa [prefixWord, tailWord_6302268, baseEnd_6302268] using wordTrace_append hprefix tailTrace_6302268
  have hstable : (prefixWord ++ tailWord_6302268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302268).length < 2 ^ (prefixWord ++ tailWord_6302268).sum := by decide
  have hdescent : baseEnd_6302268 < baseStart_6302268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302332 : List Nat := [2, 2, 2, 1, 1, 2, 6, 2, 1, 4]
def baseStart_6302332 : Nat := 118140960795 + 6302332 * 2 ^ 59
def prefixEnd_6302332 : Nat := 4983230072969 + 3 ^ 40 * 6302332 * 2
def baseEnd_6302332 : Nat := 1078708520070580443588703

theorem tailTrace_6302332 : CollatzResearch.WordTrace tailWord_6302332 prefixEnd_6302332 1078708520070580443588703 := by
  unfold tailWord_6302332
  simp only [CollatzResearch.WordTrace]
  refine ⟨114932466101867495728950625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153243288135823327638600833 114932466101867495728950625)
  ·
    refine ⟨86199349576400621796712969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114932466101867495728950625 86199349576400621796712969)
    ·
      refine ⟨64649512182300466347534727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86199349576400621796712969 64649512182300466347534727)
      ·
        refine ⟨96974268273450699521302091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64649512182300466347534727 96974268273450699521302091)
        ·
          refine ⟨145461402410176049281953137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96974268273450699521302091 145461402410176049281953137)
          ·
            refine ⟨109096051807632036961464853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145461402410176049281953137 109096051807632036961464853)
            ·
              refine ⟨5113877428482751732568665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 109096051807632036961464853 5113877428482751732568665)
              ·
                refine ⟨3835408071362063799426499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5113877428482751732568665 3835408071362063799426499)
                ·
                  refine ⟨5753112107043095699139749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835408071362063799426499 5753112107043095699139749)
                  ·
                    refine ⟨1078708520070580443588703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753112107043095699139749 1078708520070580443588703)
                    ·
                      rfl

theorem cell23_6302332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 6, 2, 1, 4].length) (baseStart_6302332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302332 prefixEnd_6302332 := by exact prefixLift 6302332
  have htrace : WordTrace (prefixWord ++ tailWord_6302332) baseStart_6302332 baseEnd_6302332 := by
    simpa [prefixWord, tailWord_6302332, baseEnd_6302332] using wordTrace_append hprefix tailTrace_6302332
  have hstable : (prefixWord ++ tailWord_6302332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302332).length < 2 ^ (prefixWord ++ tailWord_6302332).sum := by decide
  have hdescent : baseEnd_6302332 < baseStart_6302332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302371 : List Nat := [1, 1, 1, 4, 1, 1, 2, 3, 3, 6]
def baseStart_6302371 : Nat := 118140960795 + 6302371 * 2 ^ 59
def prefixEnd_6302371 : Nat := 4983230072969 + 3 ^ 40 * 6302371 * 2
def baseEnd_6302371 : Nat := 1078715195319088892726143

theorem tailTrace_6302371 : CollatzResearch.WordTrace tailWord_6302371 prefixEnd_6302371 1078715195319088892726143 := by
  unfold tailWord_6302371
  simp only [CollatzResearch.WordTrace]
  refine ⟨229866354650593701118570967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153244236433729134079047311 229866354650593701118570967)
  ·
    refine ⟨344799531975890551677856451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229866354650593701118570967 344799531975890551677856451)
    ·
      refine ⟨517199297963835827516784677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344799531975890551677856451 517199297963835827516784677)
      ·
        refine ⟨96974868368219217659397127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 517199297963835827516784677 96974868368219217659397127)
        ·
          refine ⟨145462302552328826489095691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96974868368219217659397127 145462302552328826489095691)
          ·
            refine ⟨218193453828493239733643537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145462302552328826489095691 218193453828493239733643537)
            ·
              refine ⟨163645090371369929800232653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218193453828493239733643537 163645090371369929800232653)
              ·
                refine ⟨61366908889263723675087245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 163645090371369929800232653 61366908889263723675087245)
                ·
                  refine ⟨23012590833473896378157717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61366908889263723675087245 23012590833473896378157717)
                  ·
                    refine ⟨1078715195319088892726143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23012590833473896378157717 1078715195319088892726143)
                    ·
                      rfl

theorem cell23_6302371_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 3, 3, 6].length) (baseStart_6302371 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302371 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302371 prefixEnd_6302371 := by exact prefixLift 6302371
  have htrace : WordTrace (prefixWord ++ tailWord_6302371) baseStart_6302371 baseEnd_6302371 := by
    simpa [prefixWord, tailWord_6302371, baseEnd_6302371] using wordTrace_append hprefix tailTrace_6302371
  have hstable : (prefixWord ++ tailWord_6302371).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302371).length < 2 ^ (prefixWord ++ tailWord_6302371).sum := by decide
  have hdescent : baseEnd_6302371 < baseStart_6302371 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302371) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302389 : List Nat := [1, 3, 3, 3, 1, 1, 2, 4, 1, 1, 3]
def baseStart_6302389 : Nat := 118140960795 + 6302389 * 2 ^ 59
def prefixEnd_6302389 : Nat := 4983230072969 + 3 ^ 40 * 6302389 * 2
def baseEnd_6302389 : Nat := 3236154828609047607753347

theorem tailTrace_6302389 : CollatzResearch.WordTrace tailWord_6302389 prefixEnd_6302389 3236154828609047607753347 := by
  unfold tailWord_6302389
  simp only [CollatzResearch.WordTrace]
  refine ⟨229867011164528490192726221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153244674109685660128484147 229867011164528490192726221)
  ·
    refine ⟨86200129186698183822272333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229867011164528490192726221 86200129186698183822272333)
    ·
      refine ⟨32325048445011818933352125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86200129186698183822272333 32325048445011818933352125)
      ·
        refine ⟨12121893166879432100007047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32325048445011818933352125 12121893166879432100007047)
        ·
          refine ⟨18182839750319148150010571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12121893166879432100007047 18182839750319148150010571)
          ·
            refine ⟨27274259625478722225015857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18182839750319148150010571 27274259625478722225015857)
            ·
              refine ⟨20455694719109041668761893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27274259625478722225015857 20455694719109041668761893)
              ·
                refine ⟨3835442759832945312892855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20455694719109041668761893 3835442759832945312892855)
                ·
                  refine ⟨5753164139749417969339283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3835442759832945312892855 5753164139749417969339283)
                  ·
                    refine ⟨8629746209624126954008925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5753164139749417969339283 8629746209624126954008925)
                    ·
                      refine ⟨3236154828609047607753347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8629746209624126954008925 3236154828609047607753347)
                      ·
                        rfl

theorem cell23_6302389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 2, 4, 1, 1, 3].length) (baseStart_6302389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302389 prefixEnd_6302389 := by exact prefixLift 6302389
  have htrace : WordTrace (prefixWord ++ tailWord_6302389) baseStart_6302389 baseEnd_6302389 := by
    simpa [prefixWord, tailWord_6302389, baseEnd_6302389] using wordTrace_append hprefix tailTrace_6302389
  have hstable : (prefixWord ++ tailWord_6302389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302389).length < 2 ^ (prefixWord ++ tailWord_6302389).sum := by decide
  have hdescent : baseEnd_6302389 < baseStart_6302389 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302408 : List Nat := [2, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6]
def baseStart_6302408 : Nat := 118140960795 + 6302408 * 2 ^ 59
def prefixEnd_6302408 : Nat := 4983230072969 + 3 ^ 40 * 6302408 * 2
def baseEnd_6302408 : Nat := 3236164584741483033415759

theorem tailTrace_6302408 : CollatzResearch.WordTrace tailWord_6302408 prefixEnd_6302408 3236164584741483033415759 := by
  unfold tailWord_6302408
  simp only [CollatzResearch.WordTrace]
  refine ⟨114933852075729828218833939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153245136100973104291778585 114933852075729828218833939)
  ·
    refine ⟨172400778113594742328250909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114933852075729828218833939 172400778113594742328250909)
    ·
      refine ⟨64650291792598028373094091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172400778113594742328250909 64650291792598028373094091)
      ·
        refine ⟨96975437688897042559641137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64650291792598028373094091 96975437688897042559641137)
        ·
          refine ⟨72731578266672781919730853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96975437688897042559641137 72731578266672781919730853)
          ·
            refine ⟨13637170925001146609949535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72731578266672781919730853 13637170925001146609949535)
            ·
              refine ⟨20455756387501719914924303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13637170925001146609949535 20455756387501719914924303)
              ·
                refine ⟨30683634581252579872386455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20455756387501719914924303 30683634581252579872386455)
                ·
                  refine ⟨46025451871878869808579683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30683634581252579872386455 46025451871878869808579683)
                  ·
                    refine ⟨69038177807818304712869525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 46025451871878869808579683 69038177807818304712869525)
                    ·
                      refine ⟨3236164584741483033415759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69038177807818304712869525 3236164584741483033415759)
                      ·
                        rfl

theorem cell23_6302408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 4, 1, 1, 1, 1, 6].length) (baseStart_6302408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302408 prefixEnd_6302408 := by exact prefixLift 6302408
  have htrace : WordTrace (prefixWord ++ tailWord_6302408) baseStart_6302408 baseEnd_6302408 := by
    simpa [prefixWord, tailWord_6302408, baseEnd_6302408] using wordTrace_append hprefix tailTrace_6302408
  have hstable : (prefixWord ++ tailWord_6302408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302408).length < 2 ^ (prefixWord ++ tailWord_6302408).sum := by decide
  have hdescent : baseEnd_6302408 < baseStart_6302408 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302412 : List Nat := [2, 2, 1, 5, 1, 2, 2, 2, 1, 1, 4]
def baseStart_6302412 : Nat := 118140960795 + 6302412 * 2 ^ 59
def prefixEnd_6302412 : Nat := 4983230072969 + 3 ^ 40 * 6302412 * 2
def baseEnd_6302412 : Nat := 3236166638664101017765741

theorem tailTrace_6302412 : CollatzResearch.WordTrace tailWord_6302412 prefixEnd_6302412 3236166638664101017765741 := by
  unfold tailWord_6302412
  simp only [CollatzResearch.WordTrace]
  refine ⟨114933925021722582560406745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153245233362296776747208993 114933925021722582560406745)
  ·
    refine ⟨86200443766291936920305059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114933925021722582560406745 86200443766291936920305059)
    ·
      refine ⟨129300665649437905380457589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86200443766291936920305059 129300665649437905380457589)
      ·
        refine ⟨12121937404634803629417899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 129300665649437905380457589 12121937404634803629417899)
        ·
          refine ⟨18182906106952205444126849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12121937404634803629417899 18182906106952205444126849)
          ·
            refine ⟨13637179580214154083095137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18182906106952205444126849 13637179580214154083095137)
            ·
              refine ⟨10227884685160615562321353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13637179580214154083095137 10227884685160615562321353)
              ·
                refine ⟨7670913513870461671741015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10227884685160615562321353 7670913513870461671741015)
                ·
                  refine ⟨11506370270805692507611523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7670913513870461671741015 11506370270805692507611523)
                  ·
                    refine ⟨17259555406208538761417285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11506370270805692507611523 17259555406208538761417285)
                    ·
                      refine ⟨3236166638664101017765741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17259555406208538761417285 3236166638664101017765741)
                      ·
                        rfl

theorem cell23_6302412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 2, 2, 2, 1, 1, 4].length) (baseStart_6302412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302412 prefixEnd_6302412 := by exact prefixLift 6302412
  have htrace : WordTrace (prefixWord ++ tailWord_6302412) baseStart_6302412 baseEnd_6302412 := by
    simpa [prefixWord, tailWord_6302412, baseEnd_6302412] using wordTrace_append hprefix tailTrace_6302412
  have hstable : (prefixWord ++ tailWord_6302412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302412).length < 2 ^ (prefixWord ++ tailWord_6302412).sum := by decide
  have hdescent : baseEnd_6302412 < baseStart_6302412 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302455 : List Nat := [1, 1, 3, 1, 1, 1, 3, 4, 3, 3, 2]
def baseStart_6302455 : Nat := 118140960795 + 6302455 * 2 ^ 59
def prefixEnd_6302455 : Nat := 4983230072969 + 3 ^ 40 * 6302455 * 2
def baseEnd_6302455 : Nat := 3236188718332244349528043

theorem tailTrace_6302455 : CollatzResearch.WordTrace tailWord_6302455 prefixEnd_6302455 3236188718332244349528043 := by
  unfold tailWord_6302455
  simp only [CollatzResearch.WordTrace]
  refine ⟨229869418382289383464628819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153246278921526255643085879 229869418382289383464628819)
  ·
    refine ⟨344804127573434075196943229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229869418382289383464628819 344804127573434075196943229)
    ·
      refine ⟨129301547840037778198853711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344804127573434075196943229 129301547840037778198853711)
      ·
        refine ⟨193952321760056667298280567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129301547840037778198853711 193952321760056667298280567)
        ·
          refine ⟨290928482640085000947420851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193952321760056667298280567 290928482640085000947420851)
          ·
            refine ⟨436392723960127501421131277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290928482640085000947420851 436392723960127501421131277)
            ·
              refine ⟨163647271485047813032924229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 436392723960127501421131277 163647271485047813032924229)
              ·
                refine ⟨30683863403446464943673293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163647271485047813032924229 30683863403446464943673293)
                ·
                  refine ⟨11506448776292424353877485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30683863403446464943673293 11506448776292424353877485)
                  ·
                    refine ⟨4314918291109659132704057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11506448776292424353877485 4314918291109659132704057)
                    ·
                      refine ⟨3236188718332244349528043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314918291109659132704057 3236188718332244349528043)
                      ·
                        rfl

theorem cell23_6302455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3, 3, 2].length) (baseStart_6302455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302455 prefixEnd_6302455 := by exact prefixLift 6302455
  have htrace : WordTrace (prefixWord ++ tailWord_6302455) baseStart_6302455 baseEnd_6302455 := by
    simpa [prefixWord, tailWord_6302455, baseEnd_6302455] using wordTrace_append hprefix tailTrace_6302455
  have hstable : (prefixWord ++ tailWord_6302455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302455).length < 2 ^ (prefixWord ++ tailWord_6302455).sum := by decide
  have hdescent : baseEnd_6302455 < baseStart_6302455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302472 : List Nat := [2, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2]
def baseStart_6302472 : Nat := 118140960795 + 6302472 * 2 ^ 59
def prefixEnd_6302472 : Nat := 4983230072969 + 3 ^ 40 * 6302472 * 2
def baseEnd_6302472 : Nat := 3236197447503370783015465

theorem tailTrace_6302472 : CollatzResearch.WordTrace tailWord_6302472 prefixEnd_6302472 3236197447503370783015465 := by
  unfold tailWord_6302472
  simp only [CollatzResearch.WordTrace]
  refine ⟨114935019211613897683998835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153246692282151863578665113 114935019211613897683998835)
  ·
    refine ⟨172402528817420846525998253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114935019211613897683998835 172402528817420846525998253)
    ·
      refine ⟨64650948306532817447249345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172402528817420846525998253 64650948306532817447249345)
      ·
        refine ⟨48488211229899613085437009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64650948306532817447249345 48488211229899613085437009)
        ·
          refine ⟨36366158422424709814077757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48488211229899613085437009 36366158422424709814077757)
          ·
            refine ⟨13637309408409266180279159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36366158422424709814077757 13637309408409266180279159)
            ·
              refine ⟨20455964112613899270418739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13637309408409266180279159 20455964112613899270418739)
              ·
                refine ⟨30683946168920848905628109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20455964112613899270418739 30683946168920848905628109)
                ·
                  refine ⟨11506479813345318339610541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30683946168920848905628109 11506479813345318339610541)
                  ·
                    refine ⟨4314929930004494377353953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11506479813345318339610541 4314929930004494377353953)
                    ·
                      refine ⟨3236197447503370783015465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4314929930004494377353953 3236197447503370783015465)
                      ·
                        rfl

theorem cell23_6302472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_6302472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302472 prefixEnd_6302472 := by exact prefixLift 6302472
  have htrace : WordTrace (prefixWord ++ tailWord_6302472) baseStart_6302472 baseEnd_6302472 := by
    simpa [prefixWord, tailWord_6302472, baseEnd_6302472] using wordTrace_append hprefix tailTrace_6302472
  have hstable : (prefixWord ++ tailWord_6302472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302472).length < 2 ^ (prefixWord ++ tailWord_6302472).sum := by decide
  have hdescent : baseEnd_6302472 < baseStart_6302472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302478 : List Nat := [4, 1, 1, 2, 1, 1, 1, 2, 4, 6]
def baseStart_6302478 : Nat := 118140960795 + 6302478 * 2 ^ 59
def prefixEnd_6302478 : Nat := 4983230072969 + 3 ^ 40 * 6302478 * 2
def baseEnd_6302478 : Nat := 1078733509462432586513479

theorem tailTrace_6302478 : CollatzResearch.WordTrace tailWord_6302478 prefixEnd_6302478 1078733509462432586513479 := by
  unfold tailWord_6302478
  simp only [CollatzResearch.WordTrace]
  refine ⟨28733782157650757299089511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153246838174137372261810725 28733782157650757299089511)
  ·
    refine ⟨43100673236476135948634267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28733782157650757299089511 43100673236476135948634267)
    ·
      refine ⟨64651009854714203922951401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43100673236476135948634267 64651009854714203922951401)
      ·
        refine ⟨48488257391035652942213551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64651009854714203922951401 48488257391035652942213551)
        ·
          refine ⟨72732386086553479413320327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48488257391035652942213551 72732386086553479413320327)
          ·
            refine ⟨109098579129830219119980491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72732386086553479413320327 109098579129830219119980491)
            ·
              refine ⟨163647868694745328679970737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 109098579129830219119980491 163647868694745328679970737)
              ·
                refine ⟨122735901521058996509978053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 163647868694745328679970737 122735901521058996509978053)
                ·
                  refine ⟨23012981535198561845620885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122735901521058996509978053 23012981535198561845620885)
                  ·
                    refine ⟨1078733509462432586513479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23012981535198561845620885 1078733509462432586513479)
                    ·
                      rfl

theorem cell23_6302478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 2, 4, 6].length) (baseStart_6302478 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302478 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302478 prefixEnd_6302478 := by exact prefixLift 6302478
  have htrace : WordTrace (prefixWord ++ tailWord_6302478) baseStart_6302478 baseEnd_6302478 := by
    simpa [prefixWord, tailWord_6302478, baseEnd_6302478] using wordTrace_append hprefix tailTrace_6302478
  have hstable : (prefixWord ++ tailWord_6302478).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302478).length < 2 ^ (prefixWord ++ tailWord_6302478).sum := by decide
  have hdescent : baseEnd_6302478 < baseStart_6302478 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302508 : List Nat := [2, 2, 1, 1, 1, 4, 2, 3, 7]
def baseStart_6302508 : Nat := 118140960795 + 6302508 * 2 ^ 59
def prefixEnd_6302508 : Nat := 4983230072969 + 3 ^ 40 * 6302508 * 2
def baseEnd_6302508 : Nat := 359579548089659182462811

theorem tailTrace_6302508 : CollatzResearch.WordTrace tailWord_6302508 prefixEnd_6302508 359579548089659182462811 := by
  unfold tailWord_6302508
  simp only [CollatzResearch.WordTrace]
  refine ⟨114935675725548686758154089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153247567634064915677538785 114935675725548686758154089)
  ·
    refine ⟨86201756794161515068615567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114935675725548686758154089 86201756794161515068615567)
    ·
      refine ⟨129302635191242272602923351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86201756794161515068615567 129302635191242272602923351)
      ·
        refine ⟨193953952786863408904385027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129302635191242272602923351 193953952786863408904385027)
        ·
          refine ⟨290930929180295113356577541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193953952786863408904385027 290930929180295113356577541)
          ·
            refine ⟨54549549221305333754358289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 290930929180295113356577541 54549549221305333754358289)
            ·
              refine ⟨40912161915979000315768717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54549549221305333754358289 40912161915979000315768717)
              ·
                refine ⟨15342060718492125118413269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40912161915979000315768717 15342060718492125118413269)
                ·
                  refine ⟨359579548089659182462811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15342060718492125118413269 359579548089659182462811)
                  ·
                    rfl

theorem cell23_6302508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 7].length) (baseStart_6302508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302508 prefixEnd_6302508 := by exact prefixLift 6302508
  have htrace : WordTrace (prefixWord ++ tailWord_6302508) baseStart_6302508 baseEnd_6302508 := by
    simpa [prefixWord, tailWord_6302508, baseEnd_6302508] using wordTrace_append hprefix tailTrace_6302508
  have hstable : (prefixWord ++ tailWord_6302508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302508).length < 2 ^ (prefixWord ++ tailWord_6302508).sum := by decide
  have hdescent : baseEnd_6302508 < baseStart_6302508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302515 : List Nat := [1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4]
def baseStart_6302515 : Nat := 118140960795 + 6302515 * 2 ^ 59
def prefixEnd_6302515 : Nat := 4983230072969 + 3 ^ 40 * 6302515 * 2
def baseEnd_6302515 : Nat := 3236219527171514114777767

theorem tailTrace_6302515 : CollatzResearch.WordTrace tailWord_6302515 prefixEnd_6302515 3236219527171514114777767 := by
  unfold tailWord_6302515
  simp only [CollatzResearch.WordTrace]
  refine ⟨229871606762072013711812999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153247737841381342474541999 229871606762072013711812999)
  ·
    refine ⟨344807410143108020567719499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229871606762072013711812999 344807410143108020567719499)
    ·
      refine ⟨517211115214662030851579249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344807410143108020567719499 517211115214662030851579249)
      ·
        refine ⟨387908336410996523138684437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517211115214662030851579249 387908336410996523138684437)
        ·
          refine ⟨18183203269265462022125833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 387908336410996523138684437 18183203269265462022125833)
          ·
            refine ⟨13637402451949096516594375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18183203269265462022125833 13637402451949096516594375)
            ·
              refine ⟨20456103677923644774891563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13637402451949096516594375 20456103677923644774891563)
              ·
                refine ⟨30684155516885467162337345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20456103677923644774891563 30684155516885467162337345)
                ·
                  refine ⟨23013116637664100371753009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30684155516885467162337345 23013116637664100371753009)
                  ·
                    refine ⟨17259837478248075278814757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23013116637664100371753009 17259837478248075278814757)
                    ·
                      refine ⟨3236219527171514114777767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17259837478248075278814757 3236219527171514114777767)
                      ·
                        rfl

theorem cell23_6302515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 1, 2, 2, 4].length) (baseStart_6302515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302515 prefixEnd_6302515 := by exact prefixLift 6302515
  have htrace : WordTrace (prefixWord ++ tailWord_6302515) baseStart_6302515 baseEnd_6302515 := by
    simpa [prefixWord, tailWord_6302515, baseEnd_6302515] using wordTrace_append hprefix tailTrace_6302515
  have hstable : (prefixWord ++ tailWord_6302515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302515).length < 2 ^ (prefixWord ++ tailWord_6302515).sum := by decide
  have hdescent : baseEnd_6302515 < baseStart_6302515 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302595 : List Nat := [1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3]
def baseStart_6302595 : Nat := 118140960795 + 6302595 * 2 ^ 59
def prefixEnd_6302595 : Nat := 4983230072969 + 3 ^ 40 * 6302595 * 2
def baseEnd_6302595 : Nat := 3236260605623873801777399

theorem tailTrace_6302595 : CollatzResearch.WordTrace tailWord_6302595 prefixEnd_6302595 3236260605623873801777399 := by
  unfold tailWord_6302595
  simp only [CollatzResearch.WordTrace]
  refine ⟨229874524601782187374725239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153249683067854791583150159 229874524601782187374725239)
  ·
    refine ⟨344811786902673281062087859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229874524601782187374725239 344811786902673281062087859)
    ·
      refine ⟨517217680354009921593131789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344811786902673281062087859 517217680354009921593131789)
      ·
        refine ⟨193956630132753720597424421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517217680354009921593131789 193956630132753720597424421)
        ·
          refine ⟨36366868149891322612017079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 193956630132753720597424421 36366868149891322612017079)
          ·
            refine ⟨54550302224836983918025619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36366868149891322612017079 54550302224836983918025619)
            ·
              refine ⟨81825453337255475877038429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54550302224836983918025619 81825453337255475877038429)
              ·
                refine ⟨30684545001470803453889411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 81825453337255475877038429 30684545001470803453889411)
                ·
                  refine ⟨46026817502206205180834117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30684545001470803453889411 46026817502206205180834117)
                  ·
                    refine ⟨8630028281663663471406397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46026817502206205180834117 8630028281663663471406397)
                    ·
                      refine ⟨3236260605623873801777399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8630028281663663471406397 3236260605623873801777399)
                      ·
                        rfl

theorem cell23_6302595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 3, 1, 4, 3].length) (baseStart_6302595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302595 prefixEnd_6302595 := by exact prefixLift 6302595
  have htrace : WordTrace (prefixWord ++ tailWord_6302595) baseStart_6302595 baseEnd_6302595 := by
    simpa [prefixWord, tailWord_6302595, baseEnd_6302595] using wordTrace_append hprefix tailTrace_6302595
  have hstable : (prefixWord ++ tailWord_6302595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302595).length < 2 ^ (prefixWord ++ tailWord_6302595).sum := by decide
  have hdescent : baseEnd_6302595 < baseStart_6302595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302615 : List Nat := [1, 1, 3, 3, 1, 2, 2, 4, 6]
def baseStart_6302615 : Nat := 118140960795 + 6302615 * 2 ^ 59
def prefixEnd_6302615 : Nat := 4983230072969 + 3 ^ 40 * 6302615 * 2
def baseEnd_6302615 : Nat := 359585652804107080391923

theorem tailTrace_6302615 : CollatzResearch.WordTrace tailWord_6302615 prefixEnd_6302615 359585652804107080391923 := by
  unfold tailWord_6302615
  simp only [CollatzResearch.WordTrace]
  refine ⟨229875254061709730790453299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153250169374473153860302199 229875254061709730790453299)
  ·
    refine ⟨344812881092564596185679949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229875254061709730790453299 344812881092564596185679949)
    ·
      refine ⟨129304830409711723569629981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344812881092564596185679949 129304830409711723569629981)
      ·
        refine ⟨48489311403641896338611243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129304830409711723569629981 48489311403641896338611243)
        ·
          refine ⟨72733967105462844507916865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48489311403641896338611243 72733967105462844507916865)
          ·
            refine ⟨54550475329097133380937649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72733967105462844507916865 54550475329097133380937649)
            ·
              refine ⟨40912856496822850035703237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54550475329097133380937649 40912856496822850035703237)
              ·
                refine ⟨7671160593154284381694357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40912856496822850035703237 7671160593154284381694357)
                ·
                  refine ⟨359585652804107080391923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7671160593154284381694357 359585652804107080391923)
                  ·
                    rfl

theorem cell23_6302615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 4, 6].length) (baseStart_6302615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302615 prefixEnd_6302615 := by exact prefixLift 6302615
  have htrace : WordTrace (prefixWord ++ tailWord_6302615) baseStart_6302615 baseEnd_6302615 := by
    simpa [prefixWord, tailWord_6302615, baseEnd_6302615] using wordTrace_append hprefix tailTrace_6302615
  have hstable : (prefixWord ++ tailWord_6302615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302615).length < 2 ^ (prefixWord ++ tailWord_6302615).sum := by decide
  have hdescent : baseEnd_6302615 < baseStart_6302615 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302665 : List Nat := [1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 4]
def baseStart_6302665 : Nat := 118140960795 + 6302665 * 2 ^ 59
def prefixEnd_6302665 : Nat := 4983230072969 + 3 ^ 40 * 6302665 * 2
def baseEnd_6302665 : Nat := 3236296549269688527902077

theorem tailTrace_6302665 : CollatzResearch.WordTrace tailWord_6302665 prefixEnd_6302665 3236296549269688527902077 := by
  unfold tailWord_6302665
  simp only [CollatzResearch.WordTrace]
  refine ⟨229877077711528589329773449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153251385141019059553182299 229877077711528589329773449)
  ·
    refine ⟨172407808283646441997330087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229877077711528589329773449 172407808283646441997330087)
    ·
      refine ⟨258611712425469662995995131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172407808283646441997330087 258611712425469662995995131)
      ·
        refine ⟨387917568638204494493992697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258611712425469662995995131 387917568638204494493992697)
        ·
          refine ⟨290938176478653370870494523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387917568638204494493992697 290938176478653370870494523)
          ·
            refine ⟨436407264717980056305741785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290938176478653370870494523 436407264717980056305741785)
            ·
              refine ⟨327305448538485042229306339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436407264717980056305741785 327305448538485042229306339)
              ·
                refine ⟨490958172807727563343959509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327305448538485042229306339 490958172807727563343959509)
                ·
                  refine ⟨11506832175181114765874051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 490958172807727563343959509 11506832175181114765874051)
                  ·
                    refine ⟨17260248262771672148811077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11506832175181114765874051 17260248262771672148811077)
                    ·
                      refine ⟨3236296549269688527902077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17260248262771672148811077 3236296549269688527902077)
                      ·
                        rfl

theorem cell23_6302665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 1, 7, 1, 4].length) (baseStart_6302665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302665 prefixEnd_6302665 := by exact prefixLift 6302665
  have htrace : WordTrace (prefixWord ++ tailWord_6302665) baseStart_6302665 baseEnd_6302665 := by
    simpa [prefixWord, tailWord_6302665, baseEnd_6302665] using wordTrace_append hprefix tailTrace_6302665
  have hstable : (prefixWord ++ tailWord_6302665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302665).length < 2 ^ (prefixWord ++ tailWord_6302665).sum := by decide
  have hdescent : baseEnd_6302665 < baseStart_6302665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302682 : List Nat := [3, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4]
def baseStart_6302682 : Nat := 118140960795 + 6302682 * 2 ^ 59
def prefixEnd_6302682 : Nat := 4983230072969 + 3 ^ 40 * 6302682 * 2
def baseEnd_6302682 : Nat := 3236305278440814961389499

theorem tailTrace_6302682 : CollatzResearch.WordTrace tailWord_6302682 prefixEnd_6302682 3236305278440814961389499 := by
  unfold tailWord_6302682
  simp only [CollatzResearch.WordTrace]
  refine ⟨57469424438116750308285575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153251798501644667488761533 57469424438116750308285575)
  ·
    refine ⟨86204136657175125462428363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57469424438116750308285575 86204136657175125462428363)
    ·
      refine ⟨129306204985762688193642545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86204136657175125462428363 129306204985762688193642545)
      ·
        refine ⟨96979653739322016145231909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129306204985762688193642545 96979653739322016145231909)
        ·
          refine ⟨18183685076122878027230983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96979653739322016145231909 18183685076122878027230983)
          ·
            refine ⟨27275527614184317040846475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18183685076122878027230983 27275527614184317040846475)
            ·
              refine ⟨40913291421276475561269713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27275527614184317040846475 40913291421276475561269713)
              ·
                refine ⟨30684968565957356670952285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40913291421276475561269713 30684968565957356670952285)
                ·
                  refine ⟨11506863212234008751607107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30684968565957356670952285 11506863212234008751607107)
                  ·
                    refine ⟨17260294818351013127410661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11506863212234008751607107 17260294818351013127410661)
                    ·
                      refine ⟨3236305278440814961389499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17260294818351013127410661 3236305278440814961389499)
                      ·
                        rfl

theorem cell23_6302682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 1, 2, 3, 1, 4].length) (baseStart_6302682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302682 prefixEnd_6302682 := by exact prefixLift 6302682
  have htrace : WordTrace (prefixWord ++ tailWord_6302682) baseStart_6302682 baseEnd_6302682 := by
    simpa [prefixWord, tailWord_6302682, baseEnd_6302682] using wordTrace_append hprefix tailTrace_6302682
  have hstable : (prefixWord ++ tailWord_6302682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302682).length < 2 ^ (prefixWord ++ tailWord_6302682).sum := by decide
  have hdescent : baseEnd_6302682 < baseStart_6302682 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302716 : List Nat := [2, 2, 2, 1, 2, 5, 2, 1, 1, 1, 4]
def baseStart_6302716 : Nat := 118140960795 + 6302716 * 2 ^ 59
def prefixEnd_6302716 : Nat := 4983230072969 + 3 ^ 40 * 6302716 * 2
def baseEnd_6302716 : Nat := 3236322736783067828364343

theorem tailTrace_6302716 : CollatzResearch.WordTrace tailWord_6302716 prefixEnd_6302716 3236322736783067828364343 := by
  unfold tailWord_6302716
  simp only [CollatzResearch.WordTrace]
  refine ⟨114939468917171912519940001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153252625222895883359920001 114939468917171912519940001)
  ·
    refine ⟨86204601687878934389955001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114939468917171912519940001 86204601687878934389955001)
    ·
      refine ⟨64653451265909200792466251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86204601687878934389955001 64653451265909200792466251)
      ·
        refine ⟨96980176898863801188699377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64653451265909200792466251 96980176898863801188699377)
        ·
          refine ⟨72735132674147850891524533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96980176898863801188699377 72735132674147850891524533)
          ·
            refine ⟨6818918688201361021080425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 72735132674147850891524533 6818918688201361021080425)
            ·
              refine ⟨5114189016151020765810319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6818918688201361021080425 5114189016151020765810319)
              ·
                refine ⟨7671283524226531148715479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114189016151020765810319 7671283524226531148715479)
                ·
                  refine ⟨11506925286339796723073219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671283524226531148715479 11506925286339796723073219)
                  ·
                    refine ⟨17260387929509695084609829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11506925286339796723073219 17260387929509695084609829)
                    ·
                      refine ⟨3236322736783067828364343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17260387929509695084609829 3236322736783067828364343)
                      ·
                        rfl

theorem cell23_6302716_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 2, 1, 1, 1, 4].length) (baseStart_6302716 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302716 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302716 prefixEnd_6302716 := by exact prefixLift 6302716
  have htrace : WordTrace (prefixWord ++ tailWord_6302716) baseStart_6302716 baseEnd_6302716 := by
    simpa [prefixWord, tailWord_6302716, baseEnd_6302716] using wordTrace_append hprefix tailTrace_6302716
  have hstable : (prefixWord ++ tailWord_6302716).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302716).length < 2 ^ (prefixWord ++ tailWord_6302716).sum := by decide
  have hdescent : baseEnd_6302716 < baseStart_6302716 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302716) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302776 : List Nat := [2, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2]
def baseStart_6302776 : Nat := 118140960795 + 6302776 * 2 ^ 59
def prefixEnd_6302776 : Nat := 4983230072969 + 3 ^ 40 * 6302776 * 2
def baseEnd_6302776 : Nat := 3236353545622337593614067

theorem tailTrace_6302776 : CollatzResearch.WordTrace tailWord_6302776 prefixEnd_6302776 3236353545622337593614067 := by
  unfold tailWord_6302776
  simp only [CollatzResearch.WordTrace]
  refine ⟨114940563107063227643532091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153254084142750970191376121 114940563107063227643532091)
  ·
    refine ⟨172410844660594841465298137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114940563107063227643532091 172410844660594841465298137)
    ·
      refine ⟨129308133495446131098973603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172410844660594841465298137 129308133495446131098973603)
      ·
        refine ⟨193962200243169196648460405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129308133495446131098973603 193962200243169196648460405)
        ·
          refine ⟨18183956272797112185793163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 193962200243169196648460405 18183956272797112185793163)
          ·
            refine ⟨27275934409195668278689745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18183956272797112185793163 27275934409195668278689745)
            ·
              refine ⟨20456950806896751209017309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27275934409195668278689745 20456950806896751209017309)
              ·
                refine ⟨7671356552586281703381491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20456950806896751209017309 7671356552586281703381491)
                ·
                  refine ⟨11507034828879422555072237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7671356552586281703381491 11507034828879422555072237)
                  ·
                    refine ⟨4315138060829783458152089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11507034828879422555072237 4315138060829783458152089)
                    ·
                      refine ⟨3236353545622337593614067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315138060829783458152089 3236353545622337593614067)
                      ·
                        rfl

theorem cell23_6302776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 2, 3, 1, 3, 2].length) (baseStart_6302776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302776 prefixEnd_6302776 := by exact prefixLift 6302776
  have htrace : WordTrace (prefixWord ++ tailWord_6302776) baseStart_6302776 baseEnd_6302776 := by
    simpa [prefixWord, tailWord_6302776, baseEnd_6302776] using wordTrace_append hprefix tailTrace_6302776
  have hstable : (prefixWord ++ tailWord_6302776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302776).length < 2 ^ (prefixWord ++ tailWord_6302776).sum := by decide
  have hdescent : baseEnd_6302776 < baseStart_6302776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302792 : List Nat := [2, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3]
def baseStart_6302792 : Nat := 118140960795 + 6302792 * 2 ^ 59
def prefixEnd_6302792 : Nat := 4983230072969 + 3 ^ 40 * 6302792 * 2
def baseEnd_6302792 : Nat := 3236361761312809531013993

theorem tailTrace_6302792 : CollatzResearch.WordTrace tailWord_6302792 prefixEnd_6302792 3236361761312809531013993 := by
  unfold tailWord_6302792
  simp only [CollatzResearch.WordTrace]
  refine ⟨114940854891034245009823315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153254473188045660013097753 114940854891034245009823315)
  ·
    refine ⟨172411282336551367514734973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114940854891034245009823315 172411282336551367514734973)
    ·
      refine ⟨64654230876206762818025615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172411282336551367514734973 64654230876206762818025615)
      ·
        refine ⟨96981346314310144227038423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64654230876206762818025615 96981346314310144227038423)
        ·
          refine ⟨145472019471465216340557635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96981346314310144227038423 145472019471465216340557635)
          ·
            refine ⟨218208029207197824510836453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145472019471465216340557635 218208029207197824510836453)
            ·
              refine ⟨40914005476349592095781835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218208029207197824510836453 40914005476349592095781835)
              ·
                refine ⟨61371008214524388143672753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40914005476349592095781835 61371008214524388143672753)
                ·
                  refine ⟨46028256160893291107754565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 61371008214524388143672753 46028256160893291107754565)
                  ·
                    refine ⟨8630298030167492082703981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46028256160893291107754565 8630298030167492082703981)
                    ·
                      refine ⟨3236361761312809531013993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8630298030167492082703981 3236361761312809531013993)
                      ·
                        rfl

theorem cell23_6302792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 4, 1, 2, 4, 3].length) (baseStart_6302792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302792 prefixEnd_6302792 := by exact prefixLift 6302792
  have htrace : WordTrace (prefixWord ++ tailWord_6302792) baseStart_6302792 baseEnd_6302792 := by
    simpa [prefixWord, tailWord_6302792, baseEnd_6302792] using wordTrace_append hprefix tailTrace_6302792
  have hstable : (prefixWord ++ tailWord_6302792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302792).length < 2 ^ (prefixWord ++ tailWord_6302792).sum := by decide
  have hdescent : baseEnd_6302792 < baseStart_6302792 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302812 : List Nat := [2, 2, 4, 1, 1, 1, 2, 1, 9]
def baseStart_6302812 : Nat := 118140960795 + 6302812 * 2 ^ 59
def prefixEnd_6302812 : Nat := 4983230072969 + 3 ^ 40 * 6302812 * 2
def baseEnd_6302812 : Nat := 359596892325099939195989

theorem tailTrace_6302812 : CollatzResearch.WordTrace tailWord_6302812 prefixEnd_6302812 359596892325099939195989 := by
  unfold tailWord_6302812
  simp only [CollatzResearch.WordTrace]
  refine ⟨114941219620998016717687345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153254959494664022290249793 114941219620998016717687345)
  ·
    refine ⟨86205914715748512538265509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114941219620998016717687345 86205914715748512538265509)
    ·
      refine ⟨16163609009202846100924783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86205914715748512538265509 16163609009202846100924783)
      ·
        refine ⟨24245413513804269151387175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16163609009202846100924783 24245413513804269151387175)
        ·
          refine ⟨36368120270706403727080763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24245413513804269151387175 36368120270706403727080763)
          ·
            refine ⟨54552180406059605590621145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36368120270706403727080763 54552180406059605590621145)
            ·
              refine ⟨40914135304544704192965859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54552180406059605590621145 40914135304544704192965859)
              ·
                refine ⟨61371202956817056289448789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40914135304544704192965859 61371202956817056289448789)
                ·
                  refine ⟨359596892325099939195989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61371202956817056289448789 359596892325099939195989)
                  ·
                    rfl

theorem cell23_6302812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 2, 1, 9].length) (baseStart_6302812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302812 prefixEnd_6302812 := by exact prefixLift 6302812
  have htrace : WordTrace (prefixWord ++ tailWord_6302812) baseStart_6302812 baseEnd_6302812 := by
    simpa [prefixWord, tailWord_6302812, baseEnd_6302812] using wordTrace_append hprefix tailTrace_6302812
  have hstable : (prefixWord ++ tailWord_6302812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302812).length < 2 ^ (prefixWord ++ tailWord_6302812).sum := by decide
  have hdescent : baseEnd_6302812 < baseStart_6302812 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302856 : List Nat := [2, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3]
def baseStart_6302856 : Nat := 118140960795 + 6302856 * 2 ^ 59
def prefixEnd_6302856 : Nat := 4983230072969 + 3 ^ 40 * 6302856 * 2
def baseEnd_6302856 : Nat := 3236394624074697280613699

theorem tailTrace_6302856 : CollatzResearch.WordTrace tailWord_6302856 prefixEnd_6302856 3236394624074697280613699 := by
  unfold tailWord_6302856
  simp only [CollatzResearch.WordTrace]
  refine ⟨114942022026918314474988211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153256029369224419299984281 114942022026918314474988211)
  ·
    refine ⟨172413033040377471712482317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114942022026918314474988211 172413033040377471712482317)
    ·
      refine ⟨64654887390141551892180869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172413033040377471712482317 64654887390141551892180869)
      ·
        refine ⟨12122791385651540979783913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 64654887390141551892180869 12122791385651540979783913)
        ·
          refine ⟨9092093539238655734837935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12122791385651540979783913 9092093539238655734837935)
          ·
            refine ⟨13638140308857983602256903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092093539238655734837935 13638140308857983602256903)
            ·
              refine ⟨20457210463286975403385355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638140308857983602256903 20457210463286975403385355)
              ·
                refine ⟨30685815694930463105078033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20457210463286975403385355 30685815694930463105078033)
                ·
                  refine ⟨23014361771197847328808525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30685815694930463105078033 23014361771197847328808525)
                  ·
                    refine ⟨8630385664199192748303197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23014361771197847328808525 8630385664199192748303197)
                    ·
                      refine ⟨3236394624074697280613699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8630385664199192748303197 3236394624074697280613699)
                      ·
                        rfl

theorem cell23_6302856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_6302856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302856 prefixEnd_6302856 := by exact prefixLift 6302856
  have htrace : WordTrace (prefixWord ++ tailWord_6302856) baseStart_6302856 baseEnd_6302856 := by
    simpa [prefixWord, tailWord_6302856, baseEnd_6302856] using wordTrace_append hprefix tailTrace_6302856
  have hstable : (prefixWord ++ tailWord_6302856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302856).length < 2 ^ (prefixWord ++ tailWord_6302856).sum := by decide
  have hdescent : baseEnd_6302856 < baseStart_6302856 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302876 : List Nat := [2, 2, 3, 2, 1, 4, 1, 1, 2, 5]
def baseStart_6302876 : Nat := 118140960795 + 6302876 * 2 ^ 59
def prefixEnd_6302876 : Nat := 4983230072969 + 3 ^ 40 * 6302876 * 2
def baseEnd_6302876 : Nat := 1078801631229262400787869

theorem tailTrace_6302876 : CollatzResearch.WordTrace tailWord_6302876 prefixEnd_6302876 1078801631229262400787869 := by
  unfold tailWord_6302876
  simp only [CollatzResearch.WordTrace]
  refine ⟨114942386756882086182852241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153256515675842781577136321 114942386756882086182852241)
  ·
    refine ⟨86206790067661564637139181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114942386756882086182852241 86206790067661564637139181)
    ·
      refine ⟨32327546275373086738927193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86206790067661564637139181 32327546275373086738927193)
      ·
        refine ⟨24245659706529815054195395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32327546275373086738927193 24245659706529815054195395)
        ·
          refine ⟨36368489559794722581293093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24245659706529815054195395 36368489559794722581293093)
          ·
            refine ⟨6819091792461510483992455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36368489559794722581293093 6819091792461510483992455)
            ·
              refine ⟨10228637688692265725988683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819091792461510483992455 10228637688692265725988683)
              ·
                refine ⟨15342956533038398588983025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228637688692265725988683 15342956533038398588983025)
                ·
                  refine ⟨11507217399778798941737269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15342956533038398588983025 11507217399778798941737269)
                  ·
                    refine ⟨1078801631229262400787869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 11507217399778798941737269 1078801631229262400787869)
                    ·
                      rfl

theorem cell23_6302876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 4, 1, 1, 2, 5].length) (baseStart_6302876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302876 prefixEnd_6302876 := by exact prefixLift 6302876
  have htrace : WordTrace (prefixWord ++ tailWord_6302876) baseStart_6302876 baseEnd_6302876 := by
    simpa [prefixWord, tailWord_6302876, baseEnd_6302876] using wordTrace_append hprefix tailTrace_6302876
  have hstable : (prefixWord ++ tailWord_6302876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302876).length < 2 ^ (prefixWord ++ tailWord_6302876).sum := by decide
  have hdescent : baseEnd_6302876 < baseStart_6302876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302899 : List Nat := [1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3]
def baseStart_6302899 : Nat := 118140960795 + 6302899 * 2 ^ 59
def prefixEnd_6302899 : Nat := 4983230072969 + 3 ^ 40 * 6302899 * 2
def baseEnd_6302899 : Nat := 3236416703742840612376001

theorem tailTrace_6302899 : CollatzResearch.WordTrace tailWord_6302899 prefixEnd_6302899 3236416703742840612376001 := by
  unfold tailWord_6302899
  simp only [CollatzResearch.WordTrace]
  refine ⟨229885612392680847293791751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153257074928453898195861167 229885612392680847293791751)
  ·
    refine ⟨344828418589021270940687627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229885612392680847293791751 344828418589021270940687627)
    ·
      refine ⟨517242627883531906411031441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344828418589021270940687627 517242627883531906411031441)
      ·
        refine ⟨387931970912648929808273581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517242627883531906411031441 387931970912648929808273581)
        ·
          refine ⟨145474489092243348678102593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387931970912648929808273581 145474489092243348678102593)
          ·
            refine ⟨109105866819182511508576945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145474489092243348678102593 109105866819182511508576945)
            ·
              refine ⟨81829400114386883631432709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109105866819182511508576945 81829400114386883631432709)
              ·
                refine ⟨15343012521447540680893633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81829400114386883631432709 15343012521447540680893633)
                ·
                  refine ⟨11507259391085655510670225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15343012521447540680893633 11507259391085655510670225)
                  ·
                    refine ⟨8630444543314241633002669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11507259391085655510670225 8630444543314241633002669)
                    ·
                      refine ⟨3236416703742840612376001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8630444543314241633002669 3236416703742840612376001)
                      ·
                        rfl

theorem cell23_6302899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 4, 2, 2, 3].length) (baseStart_6302899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302899 prefixEnd_6302899 := by exact prefixLift 6302899
  have htrace : WordTrace (prefixWord ++ tailWord_6302899) baseStart_6302899 baseEnd_6302899 := by
    simpa [prefixWord, tailWord_6302899, baseEnd_6302899] using wordTrace_append hprefix tailTrace_6302899
  have hstable : (prefixWord ++ tailWord_6302899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302899).length < 2 ^ (prefixWord ++ tailWord_6302899).sum := by decide
  have hdescent : baseEnd_6302899 < baseStart_6302899 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302913 : List Nat := [1, 2, 6, 1, 1, 1, 2, 1, 2, 4, 2]
def baseStart_6302913 : Nat := 118140960795 + 6302913 * 2 ^ 59
def prefixEnd_6302913 : Nat := 4983230072969 + 3 ^ 40 * 6302913 * 2
def baseEnd_6302913 : Nat := 3236423892472003557600937

theorem tailTrace_6302913 : CollatzResearch.WordTrace tailWord_6302913 prefixEnd_6302913 3236423892472003557600937 := by
  unfold tailWord_6302913
  simp only [CollatzResearch.WordTrace]
  refine ⟨229886123014630127684801393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153257415343086751789867595 229886123014630127684801393)
  ·
    refine ⟨172414592260972595763601045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229886123014630127684801393 172414592260972595763601045)
    ·
      refine ⟨8081934012233090426418799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172414592260972595763601045 8081934012233090426418799)
      ·
        refine ⟨12122901018349635639628199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8081934012233090426418799 12122901018349635639628199)
        ·
          refine ⟨18184351527524453459442299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12122901018349635639628199 18184351527524453459442299)
          ·
            refine ⟨27276527291286680189163449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18184351527524453459442299 27276527291286680189163449)
            ·
              refine ⟨20457395468465010141872587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27276527291286680189163449 20457395468465010141872587)
              ·
                refine ⟨30686093202697515212808881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20457395468465010141872587 30686093202697515212808881)
                ·
                  refine ⟨23014569902023136409606661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30686093202697515212808881 23014569902023136409606661)
                  ·
                    refine ⟨4315231856629338076801249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23014569902023136409606661 4315231856629338076801249)
                    ·
                      refine ⟨3236423892472003557600937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315231856629338076801249 3236423892472003557600937)
                      ·
                        rfl

theorem cell23_6302913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 1, 2, 4, 2].length) (baseStart_6302913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302913 prefixEnd_6302913 := by exact prefixLift 6302913
  have htrace : WordTrace (prefixWord ++ tailWord_6302913) baseStart_6302913 baseEnd_6302913 := by
    simpa [prefixWord, tailWord_6302913, baseEnd_6302913] using wordTrace_append hprefix tailTrace_6302913
  have hstable : (prefixWord ++ tailWord_6302913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302913).length < 2 ^ (prefixWord ++ tailWord_6302913).sum := by decide
  have hdescent : baseEnd_6302913 < baseStart_6302913 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302939 : List Nat := [1, 1, 1, 1, 1, 1, 1, 4, 5, 5, 2]
def baseStart_6302939 : Nat := 118140960795 + 6302939 * 2 ^ 59
def prefixEnd_6302939 : Nat := 4983230072969 + 3 ^ 40 * 6302939 * 2
def baseEnd_6302939 : Nat := 3236437242969020455875817

theorem tailTrace_6302939 : CollatzResearch.WordTrace tailWord_6302939 prefixEnd_6302939 3236437242969020455875817 := by
  unfold tailWord_6302939
  simp only [CollatzResearch.WordTrace]
  refine ⟨229887071312535934125247871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153258047541690622750165247 229887071312535934125247871)
  ·
    refine ⟨344830606968803901187871807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229887071312535934125247871 344830606968803901187871807)
    ·
      refine ⟨517245910453205851781807711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344830606968803901187871807 517245910453205851781807711)
      ·
        refine ⟨775868865679808777672711567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517245910453205851781807711 775868865679808777672711567)
        ·
          refine ⟨1163803298519713166509067351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775868865679808777672711567 1163803298519713166509067351)
          ·
            refine ⟨1745704947779569749763601027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1163803298519713166509067351 1745704947779569749763601027)
            ·
              refine ⟨2618557421669354624645401541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1745704947779569749763601027 2618557421669354624645401541)
              ·
                refine ⟨490979516563003992121012789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2618557421669354624645401541 490979516563003992121012789)
                ·
                  refine ⟨46029329677781624261344949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 490979516563003992121012789 46029329677781624261344949)
                  ·
                    refine ⟨4315249657292027274501089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46029329677781624261344949 4315249657292027274501089)
                    ·
                      refine ⟨3236437242969020455875817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315249657292027274501089 3236437242969020455875817)
                      ·
                        rfl

theorem cell23_6302939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 4, 5, 5, 2].length) (baseStart_6302939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302939 prefixEnd_6302939 := by exact prefixLift 6302939
  have htrace : WordTrace (prefixWord ++ tailWord_6302939) baseStart_6302939 baseEnd_6302939 := by
    simpa [prefixWord, tailWord_6302939, baseEnd_6302939] using wordTrace_append hprefix tailTrace_6302939
  have hstable : (prefixWord ++ tailWord_6302939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302939).length < 2 ^ (prefixWord ++ tailWord_6302939).sum := by decide
  have hdescent : baseEnd_6302939 < baseStart_6302939 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302956 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 4, 3, 2]
def baseStart_6302956 : Nat := 118140960795 + 6302956 * 2 ^ 59
def prefixEnd_6302956 : Nat := 4983230072969 + 3 ^ 40 * 6302956 * 2
def baseEnd_6302956 : Nat := 3236445972140146889363239

theorem tailTrace_6302956 : CollatzResearch.WordTrace tailWord_6302956 prefixEnd_6302956 3236445972140146889363239 := by
  unfold tailWord_6302956
  simp only [CollatzResearch.WordTrace]
  refine ⟨114943845676737173014308361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153258460902316230685744481 114943845676737173014308361)
  ·
    refine ⟨86207884257552879760731271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114943845676737173014308361 86207884257552879760731271)
    ·
      refine ⟨129311826386329319641096907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86207884257552879760731271 129311826386329319641096907)
      ·
        refine ⟨193967739579493979461645361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129311826386329319641096907 193967739579493979461645361)
        ·
          refine ⟨145475804684620484596234021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193967739579493979461645361 145475804684620484596234021)
          ·
            refine ⟨27276713378366340861793879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 145475804684620484596234021 27276713378366340861793879)
            ·
              refine ⟨40915070067549511292690819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27276713378366340861793879 40915070067549511292690819)
              ·
                refine ⟨61372605101324266939036229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40915070067549511292690819 61372605101324266939036229)
                ·
                  refine ⟨11507363456498300051069293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61372605101324266939036229 11507363456498300051069293)
                  ·
                    refine ⟨4315261296186862519150985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11507363456498300051069293 4315261296186862519150985)
                    ·
                      refine ⟨3236445972140146889363239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315261296186862519150985 3236445972140146889363239)
                      ·
                        rfl

theorem cell23_6302956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 3, 2].length) (baseStart_6302956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302956 prefixEnd_6302956 := by exact prefixLift 6302956
  have htrace : WordTrace (prefixWord ++ tailWord_6302956) baseStart_6302956 baseEnd_6302956 := by
    simpa [prefixWord, tailWord_6302956, baseEnd_6302956] using wordTrace_append hprefix tailTrace_6302956
  have hstable : (prefixWord ++ tailWord_6302956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302956).length < 2 ^ (prefixWord ++ tailWord_6302956).sum := by decide
  have hdescent : baseEnd_6302956 < baseStart_6302956 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302963 : List Nat := [1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 3]
def baseStart_6302963 : Nat := 118140960795 + 6302963 * 2 ^ 59
def prefixEnd_6302963 : Nat := 4983230072969 + 3 ^ 40 * 6302963 * 2
def baseEnd_6302963 : Nat := 3236449566504728361975707

theorem tailTrace_6302963 : CollatzResearch.WordTrace tailWord_6302963 prefixEnd_6302963 3236449566504728361975707 := by
  unfold tailWord_6302963
  simp only [CollatzResearch.WordTrace]
  refine ⟨229887946664448986224121543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153258631109632657482747695 229887946664448986224121543)
  ·
    refine ⟨344831919996673479336182315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229887946664448986224121543 344831919996673479336182315)
    ·
      refine ⟨517247879995010219004273473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344831919996673479336182315 517247879995010219004273473)
      ·
        refine ⟨387935909996257664253205105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517247879995010219004273473 387935909996257664253205105)
        ·
          refine ⟨290951932497193248189903829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 387935909996257664253205105 290951932497193248189903829)
          ·
            refine ⟨6819185917902966754450871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 290951932497193248189903829 6819185917902966754450871)
            ·
              refine ⟨10228778876854450131676307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819185917902966754450871 10228778876854450131676307)
              ·
                refine ⟨15343168315281675197514461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228778876854450131676307 15343168315281675197514461)
                ·
                  refine ⟨5753688118230628199067923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15343168315281675197514461 5753688118230628199067923)
                  ·
                    refine ⟨8630532177345942298601885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5753688118230628199067923 8630532177345942298601885)
                    ·
                      refine ⟨3236449566504728361975707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8630532177345942298601885 3236449566504728361975707)
                      ·
                        rfl

theorem cell23_6302963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 7, 1, 1, 3, 1, 3].length) (baseStart_6302963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302963 prefixEnd_6302963 := by exact prefixLift 6302963
  have htrace : WordTrace (prefixWord ++ tailWord_6302963) baseStart_6302963 baseEnd_6302963 := by
    simpa [prefixWord, tailWord_6302963, baseEnd_6302963] using wordTrace_append hprefix tailTrace_6302963
  have hstable : (prefixWord ++ tailWord_6302963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302963).length < 2 ^ (prefixWord ++ tailWord_6302963).sum := by decide
  have hdescent : baseEnd_6302963 < baseStart_6302963 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6302969 : List Nat := [1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 4]
def baseStart_6302969 : Nat := 118140960795 + 6302969 * 2 ^ 59
def prefixEnd_6302969 : Nat := 4983230072969 + 3 ^ 40 * 6302969 * 2
def baseEnd_6302969 : Nat := 3236452647388655338500679

theorem tailTrace_6302969 : CollatzResearch.WordTrace tailWord_6302969 prefixEnd_6302969 3236452647388655338500679 := by
  unfold tailWord_6302969
  simp only [CollatzResearch.WordTrace]
  refine ⟨229888165502427249248839961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153258777001618166165893307 229888165502427249248839961)
  ·
    refine ⟨172416124126820436936629971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229888165502427249248839961 172416124126820436936629971)
    ·
      refine ⟨258624186190230655404944957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172416124126820436936629971 258624186190230655404944957)
      ·
        refine ⟨96984069821336495776854359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258624186190230655404944957 96984069821336495776854359)
        ·
          refine ⟨145476104732004743665281539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96984069821336495776854359 145476104732004743665281539)
          ·
            refine ⟨218214157098007115497922309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145476104732004743665281539 218214157098007115497922309)
            ·
              refine ⟨40915154455876334155860433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 218214157098007115497922309 40915154455876334155860433)
              ·
                refine ⟨30686365841907250616895325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40915154455876334155860433 30686365841907250616895325)
                ·
                  refine ⟨11507387190715218981335747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30686365841907250616895325 11507387190715218981335747)
                  ·
                    refine ⟨17261080786072828472003621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11507387190715218981335747 17261080786072828472003621)
                    ·
                      refine ⟨3236452647388655338500679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17261080786072828472003621 3236452647388655338500679)
                      ·
                        rfl

theorem cell23_6302969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 4, 2, 3, 1, 4].length) (baseStart_6302969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6302969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6302969 prefixEnd_6302969 := by exact prefixLift 6302969
  have htrace : WordTrace (prefixWord ++ tailWord_6302969) baseStart_6302969 baseEnd_6302969 := by
    simpa [prefixWord, tailWord_6302969, baseEnd_6302969] using wordTrace_append hprefix tailTrace_6302969
  have hstable : (prefixWord ++ tailWord_6302969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6302969).length < 2 ^ (prefixWord ++ tailWord_6302969).sum := by decide
  have hdescent : baseEnd_6302969 < baseStart_6302969 := by decide
  rcases family_descends (prefixWord ++ tailWord_6302969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303013 : List Nat := [1, 3, 1, 2, 4, 2, 2, 2, 2, 4]
def baseStart_6303013 : Nat := 118140960795 + 6303013 * 2 ^ 59
def prefixEnd_6303013 : Nat := 4983230072969 + 3 ^ 40 * 6303013 * 2
def baseEnd_6303013 : Nat := 1078825080179151055450159

theorem tailTrace_6303013 : CollatzResearch.WordTrace tailWord_6303013 prefixEnd_6303013 1078825080179151055450159 := by
  unfold tailWord_6303013
  simp only [CollatzResearch.WordTrace]
  refine ⟨229889770314267844763441693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153259846876178563175627795 229889770314267844763441693)
  ·
    refine ⟨86208663867850441786290635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229889770314267844763441693 86208663867850441786290635)
    ·
      refine ⟨129312995801775662679435953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86208663867850441786290635 129312995801775662679435953)
      ·
        refine ⟨96984746851331747009576965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129312995801775662679435953 96984746851331747009576965)
        ·
          refine ⟨18184640034624702564295681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96984746851331747009576965 18184640034624702564295681)
          ·
            refine ⟨13638480025968526923221761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18184640034624702564295681 13638480025968526923221761)
            ·
              refine ⟨10228860019476395192416321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13638480025968526923221761 10228860019476395192416321)
              ·
                refine ⟨7671645014607296394312241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10228860019476395192416321 7671645014607296394312241)
                ·
                  refine ⟨5753733760955472295734181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7671645014607296394312241 5753733760955472295734181)
                  ·
                    refine ⟨1078825080179151055450159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753733760955472295734181 1078825080179151055450159)
                    ·
                      rfl

theorem cell23_6303013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 2, 2, 2, 2, 4].length) (baseStart_6303013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303013 prefixEnd_6303013 := by exact prefixLift 6303013
  have htrace : WordTrace (prefixWord ++ tailWord_6303013) baseStart_6303013 baseEnd_6303013 := by
    simpa [prefixWord, tailWord_6303013, baseEnd_6303013] using wordTrace_append hprefix tailTrace_6303013
  have hstable : (prefixWord ++ tailWord_6303013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303013).length < 2 ^ (prefixWord ++ tailWord_6303013).sum := by decide
  have hdescent : baseEnd_6303013 < baseStart_6303013 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303026 : List Nat := [3, 2, 1, 1, 4, 3, 1, 8]
def baseStart_6303026 : Nat := 118140960795 + 6303026 * 2 ^ 59
def prefixEnd_6303026 : Nat := 4983230072969 + 3 ^ 40 * 6303026 * 2
def baseEnd_6303026 : Nat := 119869700584665245018071

theorem tailTrace_6303026 : CollatzResearch.WordTrace tailWord_6303026 prefixEnd_6303026 119869700584665245018071 := by
  unfold tailWord_6303026
  simp only [CollatzResearch.WordTrace]
  refine ⟨57472561115805186995916233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153260162975480498655776621 57472561115805186995916233)
  ·
    refine ⟨43104420836853890246937175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57472561115805186995916233 43104420836853890246937175)
    ·
      refine ⟨64656631255280835370405763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43104420836853890246937175 64656631255280835370405763)
      ·
        refine ⟨96984946882921253055608645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64656631255280835370405763 96984946882921253055608645)
        ·
          refine ⟨18184677540547734947926621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96984946882921253055608645 18184677540547734947926621)
          ·
            refine ⟨6819254077705400605472483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18184677540547734947926621 6819254077705400605472483)
            ·
              refine ⟨10228881116558100908208725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819254077705400605472483 10228881116558100908208725)
              ·
                refine ⟨119869700584665245018071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 10228881116558100908208725 119869700584665245018071)
                ·
                  rfl

theorem cell23_6303026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_6303026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303026 prefixEnd_6303026 := by exact prefixLift 6303026
  have htrace : WordTrace (prefixWord ++ tailWord_6303026) baseStart_6303026 baseEnd_6303026 := by
    simpa [prefixWord, tailWord_6303026, baseEnd_6303026] using wordTrace_append hprefix tailTrace_6303026
  have hstable : (prefixWord ++ tailWord_6303026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303026).length < 2 ^ (prefixWord ++ tailWord_6303026).sum := by decide
  have hdescent : baseEnd_6303026 < baseStart_6303026 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303030 : List Nat := [5, 1, 2, 3, 1, 1, 2, 1, 1, 6]
def baseStart_6303030 : Nat := 118140960795 + 6303030 * 2 ^ 59
def prefixEnd_6303030 : Nat := 4983230072969 + 3 ^ 40 * 6303030 * 2
def baseEnd_6303030 : Nat := 1078827989902859866612633

theorem tailTrace_6303030 : CollatzResearch.WordTrace tailWord_6303030 prefixEnd_6303030 1078827989902859866612633 := by
  unfold tailWord_6303030
  simp only [CollatzResearch.WordTrace]
  refine ⟨14368149397200391041675659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153260260236804171111207029 14368149397200391041675659)
  ·
    refine ⟨21552224095800586562513489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14368149397200391041675659 21552224095800586562513489)
    ·
      refine ⟨16164168071850439921885117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21552224095800586562513489 16164168071850439921885117)
      ·
        refine ⟨6061563026943914970706919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16164168071850439921885117 6061563026943914970706919)
        ·
          refine ⟨9092344540415872456060379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061563026943914970706919 9092344540415872456060379)
          ·
            refine ⟨13638516810623808684090569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092344540415872456060379 13638516810623808684090569)
            ·
              refine ⟨10228887607967856513067927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13638516810623808684090569 10228887607967856513067927)
              ·
                refine ⟨15343331411951784769601891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228887607967856513067927 15343331411951784769601891)
                ·
                  refine ⟨23014997117927677154402837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15343331411951784769601891 23014997117927677154402837)
                  ·
                    refine ⟨1078827989902859866612633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23014997117927677154402837 1078827989902859866612633)
                    ·
                      rfl

theorem cell23_6303030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_6303030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303030 prefixEnd_6303030 := by exact prefixLift 6303030
  have htrace : WordTrace (prefixWord ++ tailWord_6303030) baseStart_6303030 baseEnd_6303030 := by
    simpa [prefixWord, tailWord_6303030, baseEnd_6303030] using wordTrace_append hprefix tailTrace_6303030
  have hstable : (prefixWord ++ tailWord_6303030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303030).length < 2 ^ (prefixWord ++ tailWord_6303030).sum := by decide
  have hdescent : baseEnd_6303030 < baseStart_6303030 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303033 : List Nat := [1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 4]
def baseStart_6303033 : Nat := 118140960795 + 6303033 * 2 ^ 59
def prefixEnd_6303033 : Nat := 4983230072969 + 3 ^ 40 * 6303033 * 2
def baseEnd_6303033 : Nat := 3236485510150543088100385

theorem tailTrace_6303033 : CollatzResearch.WordTrace tailWord_6303033 prefixEnd_6303033 3236485510150543088100385 := by
  unfold tailWord_6303033
  simp only [CollatzResearch.WordTrace]
  refine ⟨229890499774195388179169753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153260333182796925452779835 229890499774195388179169753)
  ·
    refine ⟨172417874830646541134377315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229890499774195388179169753 172417874830646541134377315)
    ·
      refine ⟨258626812245969811701565973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172417874830646541134377315 258626812245969811701565973)
      ·
        refine ⟨12123131824029834923510905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 258626812245969811701565973 12123131824029834923510905)
        ·
          refine ⟨9092348868022376192633179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12123131824029834923510905 9092348868022376192633179)
          ·
            refine ⟨13638523302033564288949769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092348868022376192633179 13638523302033564288949769)
            ·
              refine ⟨10228892476525173216712327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13638523302033564288949769 10228892476525173216712327)
              ·
                refine ⟨15343338714787759825068491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10228892476525173216712327 15343338714787759825068491)
                ·
                  refine ⟨23015008072181639737602737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15343338714787759825068491 23015008072181639737602737)
                  ·
                    refine ⟨17261256054136229803202053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23015008072181639737602737 17261256054136229803202053)
                    ·
                      refine ⟨3236485510150543088100385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17261256054136229803202053 3236485510150543088100385)
                      ·
                        rfl

theorem cell23_6303033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_6303033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303033 prefixEnd_6303033 := by exact prefixLift 6303033
  have htrace : WordTrace (prefixWord ++ tailWord_6303033) baseStart_6303033 baseEnd_6303033 := by
    simpa [prefixWord, tailWord_6303033, baseEnd_6303033] using wordTrace_append hprefix tailTrace_6303033
  have hstable : (prefixWord ++ tailWord_6303033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303033).length < 2 ^ (prefixWord ++ tailWord_6303033).sum := by decide
  have hdescent : baseEnd_6303033 < baseStart_6303033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303036 : List Nat := [2, 2, 2, 2, 1, 3, 1, 3, 1, 3, 3]
def baseStart_6303036 : Nat := 118140960795 + 6303036 * 2 ^ 59
def prefixEnd_6303036 : Nat := 4983230072969 + 3 ^ 40 * 6303036 * 2
def baseEnd_6303036 : Nat := 3236487050592506576362871

theorem tailTrace_6303036 : CollatzResearch.WordTrace tailWord_6303036 prefixEnd_6303036 3236487050592506576362871 := by
  unfold tailWord_6303036
  simp only [CollatzResearch.WordTrace]
  refine ⟨114945304596592259845764481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153260406128789679794352641 114945304596592259845764481)
  ·
    refine ⟨86208978447444194884323361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114945304596592259845764481 86208978447444194884323361)
    ·
      refine ⟨64656733835583146163242521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86208978447444194884323361 64656733835583146163242521)
      ·
        refine ⟨48492550376687359622431891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64656733835583146163242521 48492550376687359622431891)
        ·
          refine ⟨72738825565031039433647837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48492550376687359622431891 72738825565031039433647837)
          ·
            refine ⟨27277059586886639787617939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72738825565031039433647837 27277059586886639787617939)
            ·
              refine ⟨40915589380329959681426909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27277059586886639787617939 40915589380329959681426909)
              ·
                refine ⟨15343346017623734880535091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40915589380329959681426909 15343346017623734880535091)
                ·
                  refine ⟨23015019026435602320802637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15343346017623734880535091 23015019026435602320802637)
                  ·
                    refine ⟨8630632134913350870300989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23015019026435602320802637 8630632134913350870300989)
                    ·
                      refine ⟨3236487050592506576362871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8630632134913350870300989 3236487050592506576362871)
                      ·
                        rfl

theorem cell23_6303036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 3, 1, 3, 3].length) (baseStart_6303036 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303036 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303036 prefixEnd_6303036 := by exact prefixLift 6303036
  have htrace : WordTrace (prefixWord ++ tailWord_6303036) baseStart_6303036 baseEnd_6303036 := by
    simpa [prefixWord, tailWord_6303036, baseEnd_6303036] using wordTrace_append hprefix tailTrace_6303036
  have hstable : (prefixWord ++ tailWord_6303036).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303036).length < 2 ^ (prefixWord ++ tailWord_6303036).sum := by decide
  have hdescent : baseEnd_6303036 < baseStart_6303036 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303037 : List Nat := [1, 4, 1, 5, 1, 1, 1, 2, 3, 2, 2]
def baseStart_6303037 : Nat := 118140960795 + 6303037 * 2 ^ 59
def prefixEnd_6303037 : Nat := 4983230072969 + 3 ^ 40 * 6303037 * 2
def baseEnd_6303037 : Nat := 3236487564073161072450367

theorem tailTrace_6303037 : CollatzResearch.WordTrace tailWord_6303037 prefixEnd_6303037 3236487564073161072450367 := by
  unfold tailWord_6303037
  simp only [CollatzResearch.WordTrace]
  refine ⟨229890645666180896862315365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153260430444120597908210243 229890645666180896862315365)
  ·
    refine ⟨43104496062408918161684131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229890645666180896862315365 43104496062408918161684131)
    ·
      refine ⟨64656744093613377242526197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43104496062408918161684131 64656744093613377242526197)
      ·
        refine ⟨6061569758776254116486831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 64656744093613377242526197 6061569758776254116486831)
        ·
          refine ⟨9092354638164381174730247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061569758776254116486831 9092354638164381174730247)
          ·
            refine ⟨13638531957246571762095371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092354638164381174730247 13638531957246571762095371)
            ·
              refine ⟨20457797935869857643143057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638531957246571762095371 20457797935869857643143057)
              ·
                refine ⟨15343348451902393232357293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20457797935869857643143057 15343348451902393232357293)
                ·
                  refine ⟨5753755669463397462133985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15343348451902393232357293 5753755669463397462133985)
                  ·
                    refine ⟨4315316752097548096600489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5753755669463397462133985 4315316752097548096600489)
                    ·
                      refine ⟨3236487564073161072450367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315316752097548096600489 3236487564073161072450367)
                      ·
                        rfl

theorem cell23_6303037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_6303037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303037 prefixEnd_6303037 := by exact prefixLift 6303037
  have htrace : WordTrace (prefixWord ++ tailWord_6303037) baseStart_6303037 baseEnd_6303037 := by
    simpa [prefixWord, tailWord_6303037, baseEnd_6303037] using wordTrace_append hprefix tailTrace_6303037
  have hstable : (prefixWord ++ tailWord_6303037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303037).length < 2 ^ (prefixWord ++ tailWord_6303037).sum := by decide
  have hdescent : baseEnd_6303037 < baseStart_6303037 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303099 : List Nat := [1, 1, 1, 1, 1, 6, 1, 4, 7]
def baseStart_6303099 : Nat := 118140960795 + 6303099 * 2 ^ 59
def prefixEnd_6303099 : Nat := 4983230072969 + 3 ^ 40 * 6303099 * 2
def baseEnd_6303099 : Nat := 359613266652637758875009

theorem tailTrace_6303099 : CollatzResearch.WordTrace tailWord_6303099 prefixEnd_6303099 359613266652637758875009 := by
  unfold tailWord_6303099
  simp only [CollatzResearch.WordTrace]
  refine ⟨229892906991956281451072351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153261937994637520967381567 229892906991956281451072351)
  ·
    refine ⟨344839360487934422176608527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229892906991956281451072351 344839360487934422176608527)
    ·
      refine ⟨517259040731901633264912791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344839360487934422176608527 517259040731901633264912791)
      ·
        refine ⟨775888561097852449897369187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517259040731901633264912791 775888561097852449897369187)
        ·
          refine ⟨1163832841646778674846053781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775888561097852449897369187 1163832841646778674846053781)
          ·
            refine ⟨54554664452192750383408771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1163832841646778674846053781 54554664452192750383408771)
            ·
              refine ⟨81831996678289125575113157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54554664452192750383408771 81831996678289125575113157)
              ·
                refine ⟨15343499377179211045333717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 81831996678289125575113157 15343499377179211045333717)
                ·
                  refine ⟨359613266652637758875009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15343499377179211045333717 359613266652637758875009)
                  ·
                    rfl

theorem cell23_6303099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 4, 7].length) (baseStart_6303099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303099 prefixEnd_6303099 := by exact prefixLift 6303099
  have htrace : WordTrace (prefixWord ++ tailWord_6303099) baseStart_6303099 baseEnd_6303099 := by
    simpa [prefixWord, tailWord_6303099, baseEnd_6303099] using wordTrace_append hprefix tailTrace_6303099
  have hstable : (prefixWord ++ tailWord_6303099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303099).length < 2 ^ (prefixWord ++ tailWord_6303099).sum := by decide
  have hdescent : baseEnd_6303099 < baseStart_6303099 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303133 : List Nat := [1, 4, 2, 1, 3, 3, 1, 1, 7]
def baseStart_6303133 : Nat := 118140960795 + 6303133 * 2 ^ 59
def prefixEnd_6303133 : Nat := 4983230072969 + 3 ^ 40 * 6303133 * 2
def baseEnd_6303133 : Nat := 359615206468443632983325

theorem tailTrace_6303133 : CollatzResearch.WordTrace tailWord_6303133 prefixEnd_6303133 359615206468443632983325 := by
  unfold tailWord_6303133
  simp only [CollatzResearch.WordTrace]
  refine ⟨229894147073833105257810053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153262764715888736838540035 229894147073833105257810053)
  ·
    refine ⟨43105152576343707235839385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229894147073833105257810053 43105152576343707235839385)
    ·
      refine ⟨32328864432257780426879539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43105152576343707235839385 32328864432257780426879539)
      ·
        refine ⟨48493296648386670640319309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32328864432257780426879539 48493296648386670640319309)
        ·
          refine ⟨18184986243145001490119741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48493296648386670640319309 18184986243145001490119741)
          ·
            refine ⟨6819369841179375558794903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18184986243145001490119741 6819369841179375558794903)
            ·
              refine ⟨10229054761769063338192355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819369841179375558794903 10229054761769063338192355)
              ·
                refine ⟨15343582142653595007288533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10229054761769063338192355 15343582142653595007288533)
                ·
                  refine ⟨359615206468443632983325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15343582142653595007288533 359615206468443632983325)
                  ·
                    rfl

theorem cell23_6303133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 3, 1, 1, 7].length) (baseStart_6303133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303133 prefixEnd_6303133 := by exact prefixLift 6303133
  have htrace : WordTrace (prefixWord ++ tailWord_6303133) baseStart_6303133 baseEnd_6303133 := by
    simpa [prefixWord, tailWord_6303133, baseEnd_6303133] using wordTrace_append hprefix tailTrace_6303133
  have hstable : (prefixWord ++ tailWord_6303133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303133).length < 2 ^ (prefixWord ++ tailWord_6303133).sum := by decide
  have hdescent : baseEnd_6303133 < baseStart_6303133 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303144 : List Nat := [2, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2]
def baseStart_6303144 : Nat := 118140960795 + 6303144 * 2 ^ 59
def prefixEnd_6303144 : Nat := 4983230072969 + 3 ^ 40 * 6303144 * 2
def baseEnd_6303144 : Nat := 3236542506503192153812375

theorem tailTrace_6303144 : CollatzResearch.WordTrace tailWord_6303144 prefixEnd_6303144 3236542506503192153812375 := by
  unfold tailWord_6303144
  simp only [CollatzResearch.WordTrace]
  refine ⟨114947274138396627068230243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153263032184528836090973657 114947274138396627068230243)
  ·
    refine ⟨172420911207594940602345365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114947274138396627068230243 172420911207594940602345365)
    ·
      refine ⟨8082230212856012840734939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 172420911207594940602345365 8082230212856012840734939)
      ·
        refine ⟨12123345319284019261102409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082230212856012840734939 12123345319284019261102409)
        ·
          refine ⟨9092508989463014445826807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12123345319284019261102409 9092508989463014445826807)
          ·
            refine ⟨13638763484194521668740211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092508989463014445826807 13638763484194521668740211)
            ·
              refine ⟨20458145226291782503110317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638763484194521668740211 20458145226291782503110317)
              ·
                refine ⟨7671804459859418438666369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20458145226291782503110317 7671804459859418438666369)
                ·
                  refine ⟨5753853344894563828999777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7671804459859418438666369 5753853344894563828999777)
                  ·
                    refine ⟨4315390008670922871749833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5753853344894563828999777 4315390008670922871749833)
                    ·
                      refine ⟨3236542506503192153812375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315390008670922871749833 3236542506503192153812375)
                      ·
                        rfl

theorem cell23_6303144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 1, 1, 3, 2, 2, 2].length) (baseStart_6303144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303144 prefixEnd_6303144 := by exact prefixLift 6303144
  have htrace : WordTrace (prefixWord ++ tailWord_6303144) baseStart_6303144 baseEnd_6303144 := by
    simpa [prefixWord, tailWord_6303144, baseEnd_6303144] using wordTrace_append hprefix tailTrace_6303144
  have hstable : (prefixWord ++ tailWord_6303144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303144).length < 2 ^ (prefixWord ++ tailWord_6303144).sum := by decide
  have hdescent : baseEnd_6303144 < baseStart_6303144 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303210 : List Nat := [3, 1, 3, 1, 4, 1, 1, 2, 3, 4]
def baseStart_6303210 : Nat := 118140960795 + 6303210 * 2 ^ 59
def prefixEnd_6303210 : Nat := 4983230072969 + 3 ^ 40 * 6303210 * 2
def baseEnd_6303210 : Nat := 1078858798742129631862357

theorem tailTrace_6303210 : CollatzResearch.WordTrace tailWord_6303210 prefixEnd_6303210 1078858798742129631862357 := by
  unfold tailWord_6303210
  simp only [CollatzResearch.WordTrace]
  refine ⟨57474238873638536852090771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153264636996369431605575389 57474238873638536852090771)
  ·
    refine ⟨86211358310457805278136157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57474238873638536852090771 86211358310457805278136157)
    ·
      refine ⟨32329259366421676979301059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86211358310457805278136157 32329259366421676979301059)
      ·
        refine ⟨48493889049632515468951589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32329259366421676979301059 48493889049632515468951589)
        ·
          refine ⟨9092604196806096650428423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48493889049632515468951589 9092604196806096650428423)
          ·
            refine ⟨13638906295209144975642635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9092604196806096650428423 13638906295209144975642635)
            ·
              refine ⟨20458359442813717463463953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13638906295209144975642635 20458359442813717463463953)
              ·
                refine ⟨15343769582110288097597965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20458359442813717463463953 15343769582110288097597965)
                ·
                  refine ⟨5753913593291358036599237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15343769582110288097597965 5753913593291358036599237)
                  ·
                    refine ⟨1078858798742129631862357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753913593291358036599237 1078858798742129631862357)
                    ·
                      rfl

theorem cell23_6303210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 1, 1, 2, 3, 4].length) (baseStart_6303210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303210 prefixEnd_6303210 := by exact prefixLift 6303210
  have htrace : WordTrace (prefixWord ++ tailWord_6303210) baseStart_6303210 baseEnd_6303210 := by
    simpa [prefixWord, tailWord_6303210, baseEnd_6303210] using wordTrace_append hprefix tailTrace_6303210
  have hstable : (prefixWord ++ tailWord_6303210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303210).length < 2 ^ (prefixWord ++ tailWord_6303210).sum := by decide
  have hdescent : baseEnd_6303210 < baseStart_6303210 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303283 : List Nat := [1, 1, 1, 2, 4, 3, 1, 2, 4, 4]
def baseStart_6303283 : Nat := 118140960795 + 6303283 * 2 ^ 59
def prefixEnd_6303283 : Nat := 4983230072969 + 3 ^ 40 * 6303283 * 2
def baseEnd_6303283 : Nat := 1078871293438055703324745

theorem tailTrace_6303283 : CollatzResearch.WordTrace tailWord_6303283 prefixEnd_6303283 1078871293438055703324745 := by
  unfold tailWord_6303283
  simp only [CollatzResearch.WordTrace]
  refine ⟨229899618023289680875770503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153266412015526453917180335 229899618023289680875770503)
  ·
    refine ⟨344849427034934521313655755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229899618023289680875770503 344849427034934521313655755)
    ·
      refine ⟨517274140552401781970483633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344849427034934521313655755 517274140552401781970483633)
      ·
        refine ⟨387955605414301336477862725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 517274140552401781970483633 387955605414301336477862725)
        ·
          refine ⟨72741676015181500589599261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 387955605414301336477862725 72741676015181500589599261)
          ·
            refine ⟨27278128505693062721099723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72741676015181500589599261 27278128505693062721099723)
            ·
              refine ⟨40917192758539594081649585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27278128505693062721099723 40917192758539594081649585)
              ·
                refine ⟨30687894568904695561237189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40917192758539594081649585 30687894568904695561237189)
                ·
                  refine ⟨5753980231669630417731973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30687894568904695561237189 5753980231669630417731973)
                  ·
                    refine ⟨1078871293438055703324745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5753980231669630417731973 1078871293438055703324745)
                    ·
                      rfl

theorem cell23_6303283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 3, 1, 2, 4, 4].length) (baseStart_6303283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303283 prefixEnd_6303283 := by exact prefixLift 6303283
  have htrace : WordTrace (prefixWord ++ tailWord_6303283) baseStart_6303283 baseEnd_6303283 := by
    simpa [prefixWord, tailWord_6303283, baseEnd_6303283] using wordTrace_append hprefix tailTrace_6303283
  have hstable : (prefixWord ++ tailWord_6303283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303283).length < 2 ^ (prefixWord ++ tailWord_6303283).sum := by decide
  have hdescent : baseEnd_6303283 < baseStart_6303283 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303357 : List Nat := [1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 3]
def baseStart_6303357 : Nat := 118140960795 + 6303357 * 2 ^ 59
def prefixEnd_6303357 : Nat := 4983230072969 + 3 ^ 40 * 6303357 * 2
def baseEnd_6303357 : Nat := 3236651877882599820448895

theorem tailTrace_6303357 : CollatzResearch.WordTrace tailWord_6303357 prefixEnd_6303357 3236651877882599820448895 := by
  unfold tailWord_6303357
  simp only [CollatzResearch.WordTrace]
  refine ⟨229902317025021591513964325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153268211350014394342642883 229902317025021591513964325)
  ·
    refine ⟨43106684442191548408868311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229902317025021591513964325 43106684442191548408868311)
    ·
      refine ⟨64660026663287322613302467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43106684442191548408868311 64660026663287322613302467)
      ·
        refine ⟨96990039994930983919953701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64660026663287322613302467 96990039994930983919953701)
        ·
          refine ⟨18185632499049559484991319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96990039994930983919953701 18185632499049559484991319)
          ·
            refine ⟨27278448748574339227486979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18185632499049559484991319 27278448748574339227486979)
            ·
              refine ⟨40917673122861508841230469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27278448748574339227486979 40917673122861508841230469)
              ·
                refine ⟨7672063710536532907730713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40917673122861508841230469 7672063710536532907730713)
                ·
                  refine ⟨5754047782902399680798035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7672063710536532907730713 5754047782902399680798035)
                  ·
                    refine ⟨8631071674353599521197053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5754047782902399680798035 8631071674353599521197053)
                    ·
                      refine ⟨3236651877882599820448895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631071674353599521197053 3236651877882599820448895)
                      ·
                        rfl

theorem cell23_6303357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 1, 4, 2, 1, 3].length) (baseStart_6303357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303357 prefixEnd_6303357 := by exact prefixLift 6303357
  have htrace : WordTrace (prefixWord ++ tailWord_6303357) baseStart_6303357 baseEnd_6303357 := by
    simpa [prefixWord, tailWord_6303357, baseEnd_6303357] using wordTrace_append hprefix tailTrace_6303357
  have hstable : (prefixWord ++ tailWord_6303357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303357).length < 2 ^ (prefixWord ++ tailWord_6303357).sum := by decide
  have hdescent : baseEnd_6303357 < baseStart_6303357 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303420 : List Nat := [2, 2, 2, 3, 1, 3, 2, 1, 7]
def baseStart_6303420 : Nat := 118140960795 + 6303420 * 2 ^ 59
def prefixEnd_6303420 : Nat := 4983230072969 + 3 ^ 40 * 6303420 * 2
def baseEnd_6303420 : Nat := 359631580795981452662345

theorem tailTrace_6303420 : CollatzResearch.WordTrace tailWord_6303420 prefixEnd_6303420 359631580795981452662345 := by
  unfold tailWord_6303420
  simp only [CollatzResearch.WordTrace]
  refine ⟨114952307411896676636753857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153269743215862235515671809 114952307411896676636753857)
  ·
    refine ⟨86214230558922507477565393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114952307411896676636753857 86214230558922507477565393)
    ·
      refine ⟨64660672919191880608174045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86214230558922507477565393 64660672919191880608174045)
      ·
        refine ⟨24247752344696955228065267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 64660672919191880608174045 24247752344696955228065267)
        ·
          refine ⟨36371628517045432842097901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24247752344696955228065267 36371628517045432842097901)
          ·
            refine ⟨13639360693892037315786713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36371628517045432842097901 13639360693892037315786713)
            ·
              refine ⟨10229520520419027986840035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13639360693892037315786713 10229520520419027986840035)
              ·
                refine ⟨15344280780628541980260053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10229520520419027986840035 15344280780628541980260053)
                ·
                  refine ⟨359631580795981452662345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15344280780628541980260053 359631580795981452662345)
                  ·
                    rfl

theorem cell23_6303420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 3, 2, 1, 7].length) (baseStart_6303420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303420 prefixEnd_6303420 := by exact prefixLift 6303420
  have htrace : WordTrace (prefixWord ++ tailWord_6303420) baseStart_6303420 baseEnd_6303420 := by
    simpa [prefixWord, tailWord_6303420, baseEnd_6303420] using wordTrace_append hprefix tailTrace_6303420
  have hstable : (prefixWord ++ tailWord_6303420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303420).length < 2 ^ (prefixWord ++ tailWord_6303420).sum := by decide
  have hdescent : baseEnd_6303420 < baseStart_6303420 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303437 : List Nat := [1, 6, 2, 1, 1, 1, 2, 2, 7]
def baseStart_6303437 : Nat := 118140960795 + 6303437 * 2 ^ 59
def prefixEnd_6303437 : Nat := 4983230072969 + 3 ^ 40 * 6303437 * 2
def baseEnd_6303437 : Nat := 359632550703884389716503

theorem tailTrace_6303437 : CollatzResearch.WordTrace tailWord_6303437 prefixEnd_6303437 359632550703884389716503 := by
  unfold tailWord_6303437
  simp only [CollatzResearch.WordTrace]
  refine ⟨229905234864731765176876565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153270156576487843451251043 229905234864731765176876565)
  ·
    refine ⟨10776807884284301492666089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 229905234864731765176876565 10776807884284301492666089)
    ·
      refine ⟨8082605913213226119499567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10776807884284301492666089 8082605913213226119499567)
      ·
        refine ⟨12123908869819839179249351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8082605913213226119499567 12123908869819839179249351)
        ·
          refine ⟨18185863304729758768874027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12123908869819839179249351 18185863304729758768874027)
          ·
            refine ⟨27278794957094638153311041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18185863304729758768874027 27278794957094638153311041)
            ·
              refine ⟨20459096217820978614983281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27278794957094638153311041 20459096217820978614983281)
              ·
                refine ⟨15344322163365733961237461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20459096217820978614983281 15344322163365733961237461)
                ·
                  refine ⟨359632550703884389716503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 15344322163365733961237461 359632550703884389716503)
                  ·
                    rfl

theorem cell23_6303437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_6303437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303437 prefixEnd_6303437 := by exact prefixLift 6303437
  have htrace : WordTrace (prefixWord ++ tailWord_6303437) baseStart_6303437 baseEnd_6303437 := by
    simpa [prefixWord, tailWord_6303437, baseEnd_6303437] using wordTrace_append hprefix tailTrace_6303437
  have hstable : (prefixWord ++ tailWord_6303437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303437).length < 2 ^ (prefixWord ++ tailWord_6303437).sum := by decide
  have hdescent : baseEnd_6303437 < baseStart_6303437 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303480 : List Nat := [2, 1, 2, 1, 1, 2, 2, 5, 3, 4]
def baseStart_6303480 : Nat := 118140960795 + 6303480 * 2 ^ 59
def prefixEnd_6303480 : Nat := 4983230072969 + 3 ^ 40 * 6303480 * 2
def baseEnd_6303480 : Nat := 1078905012001034279736943

theorem tailTrace_6303480 : CollatzResearch.WordTrace tailWord_6303480 prefixEnd_6303480 1078905012001034279736943 := by
  unfold tailWord_6303480
  simp only [CollatzResearch.WordTrace]
  refine ⟨114953401601787991760345947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153271202135717322347127929 114953401601787991760345947)
  ·
    refine ⟨172430102402681987640518921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114953401601787991760345947 172430102402681987640518921)
    ·
      refine ⟨129322576802011490730389191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172430102402681987640518921 129322576802011490730389191)
      ·
        refine ⟨193983865203017236095583787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129322576802011490730389191 193983865203017236095583787)
        ·
          refine ⟨290975797804525854143375681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193983865203017236095583787 290975797804525854143375681)
          ·
            refine ⟨218231848353394390607531761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290975797804525854143375681 218231848353394390607531761)
            ·
              refine ⟨163673886265045792955648821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218231848353394390607531761 163673886265045792955648821)
              ·
                refine ⟨15344426837348043089592077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 163673886265045792955648821 15344426837348043089592077)
                ·
                  refine ⟨5754160064005516158597029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15344426837348043089592077 5754160064005516158597029)
                  ·
                    refine ⟨1078905012001034279736943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5754160064005516158597029 1078905012001034279736943)
                    ·
                      rfl

theorem cell23_6303480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 2, 5, 3, 4].length) (baseStart_6303480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303480 prefixEnd_6303480 := by exact prefixLift 6303480
  have htrace : WordTrace (prefixWord ++ tailWord_6303480) baseStart_6303480 baseEnd_6303480 := by
    simpa [prefixWord, tailWord_6303480, baseEnd_6303480] using wordTrace_append hprefix tailTrace_6303480
  have hstable : (prefixWord ++ tailWord_6303480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303480).length < 2 ^ (prefixWord ++ tailWord_6303480).sum := by decide
  have hdescent : baseEnd_6303480 < baseStart_6303480 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303483 : List Nat := [1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_6303483 : Nat := 118140960795 + 6303483 * 2 ^ 59
def prefixEnd_6303483 : Nat := 4983230072969 + 3 ^ 40 * 6303483 * 2
def baseEnd_6303483 : Nat := 3236716576445066327473315

theorem tailTrace_6303483 : CollatzResearch.WordTrace tailWord_6303483 prefixEnd_6303483 3236716576445066327473315 := by
  unfold tailWord_6303483
  simp only [CollatzResearch.WordTrace]
  refine ⟨229906912622565115033051103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153271275081710076688700735 229906912622565115033051103)
  ·
    refine ⟨344860368933847672549576655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229906912622565115033051103 344860368933847672549576655)
    ·
      refine ⟨517290553400771508824364983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344860368933847672549576655 517290553400771508824364983)
      ·
        refine ⟨775935830101157263236547475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517290553400771508824364983 775935830101157263236547475)
        ·
          refine ⟨1163903745151735894854821213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775935830101157263236547475 1163903745151735894854821213)
          ·
            refine ⟨436463904431900960570557955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1163903745151735894854821213 436463904431900960570557955)
            ·
              refine ⟨654695856647851440855836933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436463904431900960570557955 654695856647851440855836933)
              ·
                refine ⟨122755473121472145160469425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 654695856647851440855836933 122755473121472145160469425)
                ·
                  refine ⟨92066604841104108870352069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 122755473121472145160469425 92066604841104108870352069)
                  ·
                    refine ⟨17262488407707020413191013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92066604841104108870352069 17262488407707020413191013)
                    ·
                      refine ⟨3236716576445066327473315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17262488407707020413191013 3236716576445066327473315)
                      ·
                        rfl

theorem cell23_6303483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_6303483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303483 prefixEnd_6303483 := by exact prefixLift 6303483
  have htrace : WordTrace (prefixWord ++ tailWord_6303483) baseStart_6303483 baseEnd_6303483 := by
    simpa [prefixWord, tailWord_6303483, baseEnd_6303483] using wordTrace_append hprefix tailTrace_6303483
  have hstable : (prefixWord ++ tailWord_6303483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303483).length < 2 ^ (prefixWord ++ tailWord_6303483).sum := by decide
  have hdescent : baseEnd_6303483 < baseStart_6303483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303558 : List Nat := [6, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3]
def baseStart_6303558 : Nat := 118140960795 + 6303558 * 2 ^ 59
def prefixEnd_6303558 : Nat := 4983230072969 + 3 ^ 40 * 6303558 * 2
def baseEnd_6303558 : Nat := 3236755087494153534035471

theorem tailTrace_6303558 : CollatzResearch.WordTrace tailWord_6303558 prefixEnd_6303558 3236755087494153534035471 := by
  unfold tailWord_6303558
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184676503040418838813479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153273098731528935228020885 7184676503040418838813479)
  ·
    refine ⟨10777014754560628258220219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7184676503040418838813479 10777014754560628258220219)
    ·
      refine ⟨16165522131840942387330329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10777014754560628258220219 16165522131840942387330329)
      ·
        refine ⟨12124141598880706790497747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16165522131840942387330329 12124141598880706790497747)
        ·
          refine ⟨18186212398321060185746621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12124141598880706790497747 18186212398321060185746621)
          ·
            refine ⟨6819829649370397569654983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18186212398321060185746621 6819829649370397569654983)
            ·
              refine ⟨10229744474055596354482475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819829649370397569654983 10229744474055596354482475)
              ·
                refine ⟨15344616711083394531723713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10229744474055596354482475 15344616711083394531723713)
                ·
                  refine ⟨11508462533312545898792785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15344616711083394531723713 11508462533312545898792785)
                  ·
                    refine ⟨8631346899984409424094589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11508462533312545898792785 8631346899984409424094589)
                    ·
                      refine ⟨3236755087494153534035471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631346899984409424094589 3236755087494153534035471)
                      ·
                        rfl

theorem cell23_6303558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 3, 1, 1, 2, 2, 3].length) (baseStart_6303558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303558 prefixEnd_6303558 := by exact prefixLift 6303558
  have htrace : WordTrace (prefixWord ++ tailWord_6303558) baseStart_6303558 baseEnd_6303558 := by
    simpa [prefixWord, tailWord_6303558, baseEnd_6303558] using wordTrace_append hprefix tailTrace_6303558
  have hstable : (prefixWord ++ tailWord_6303558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303558).length < 2 ^ (prefixWord ++ tailWord_6303558).sum := by decide
  have hdescent : baseEnd_6303558 < baseStart_6303558 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303564 : List Nat := [2, 2, 1, 3, 4, 1, 1, 1, 1, 5, 2]
def baseStart_6303564 : Nat := 118140960795 + 6303564 * 2 ^ 59
def prefixEnd_6303564 : Nat := 4983230072969 + 3 ^ 40 * 6303564 * 2
def baseEnd_6303564 : Nat := 3236758168378080510560443

theorem tailTrace_6303564 : CollatzResearch.WordTrace tailWord_6303564 prefixEnd_6303564 3236758168378080510560443 := by
  unfold tailWord_6303564
  simp only [CollatzResearch.WordTrace]
  refine ⟨114954933467635832933374873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153273244623514443911166497 114954933467635832933374873)
  ·
    refine ⟨86216200100726874700031155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114954933467635832933374873 86216200100726874700031155)
    ·
      refine ⟨129324300151090312050046733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86216200100726874700031155 129324300151090312050046733)
      ·
        refine ⟨48496612556658867018767525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129324300151090312050046733 48496612556658867018767525)
        ·
          refine ⟨9093114854373537566018911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48496612556658867018767525 9093114854373537566018911)
          ·
            refine ⟨13639672281560306349028367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9093114854373537566018911 13639672281560306349028367)
            ·
              refine ⟨20459508422340459523542551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13639672281560306349028367 20459508422340459523542551)
              ·
                refine ⟨30689262633510689285313827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20459508422340459523542551 30689262633510689285313827)
                ·
                  refine ⟨46033893950266033927970741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30689262633510689285313827 46033893950266033927970741)
                  ·
                    refine ⟨4315677557837440680747257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 46033893950266033927970741 4315677557837440680747257)
                    ·
                      refine ⟨3236758168378080510560443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315677557837440680747257 3236758168378080510560443)
                      ·
                        rfl

theorem cell23_6303564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 4, 1, 1, 1, 1, 5, 2].length) (baseStart_6303564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303564 prefixEnd_6303564 := by exact prefixLift 6303564
  have htrace : WordTrace (prefixWord ++ tailWord_6303564) baseStart_6303564 baseEnd_6303564 := by
    simpa [prefixWord, tailWord_6303564, baseEnd_6303564] using wordTrace_append hprefix tailTrace_6303564
  have hstable : (prefixWord ++ tailWord_6303564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303564).length < 2 ^ (prefixWord ++ tailWord_6303564).sum := by decide
  have hdescent : baseEnd_6303564 < baseStart_6303564 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303577 : List Nat := [1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 4]
def baseStart_6303577 : Nat := 118140960795 + 6303577 * 2 ^ 59
def prefixEnd_6303577 : Nat := 4983230072969 + 3 ^ 40 * 6303577 * 2
def baseEnd_6303577 : Nat := 3236764843626588959697883

theorem tailTrace_6303577 : CollatzResearch.WordTrace tailWord_6303577 prefixEnd_6303577 3236764843626588959697883 := by
  unfold tailWord_6303577
  simp only [CollatzResearch.WordTrace]
  refine ⟨229910341084224569086972985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153273560722816379391315323 229910341084224569086972985)
  ·
    refine ⟨172432755813168426815229739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229910341084224569086972985 172432755813168426815229739)
    ·
      refine ⟨258649133719752640222844609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172432755813168426815229739 258649133719752640222844609)
      ·
        refine ⟨193986850289814480167133457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258649133719752640222844609 193986850289814480167133457)
        ·
          refine ⟨145490137717360860125350093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 193986850289814480167133457 145490137717360860125350093)
          ·
            refine ⟨54558801644010322547006285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145490137717360860125350093 54558801644010322547006285)
            ·
              refine ⟨20459550616503870955127357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54558801644010322547006285 20459550616503870955127357)
              ·
                refine ⟨7672331481188951608172759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20459550616503870955127357 7672331481188951608172759)
                ·
                  refine ⟨11508497221783427412259139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7672331481188951608172759 11508497221783427412259139)
                  ·
                    refine ⟨17262745832675141118388709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11508497221783427412259139 17262745832675141118388709)
                    ·
                      refine ⟨3236764843626588959697883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17262745832675141118388709 3236764843626588959697883)
                      ·
                        rfl

theorem cell23_6303577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 3, 3, 1, 1, 4].length) (baseStart_6303577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303577 prefixEnd_6303577 := by exact prefixLift 6303577
  have htrace : WordTrace (prefixWord ++ tailWord_6303577) baseStart_6303577 baseEnd_6303577 := by
    simpa [prefixWord, tailWord_6303577, baseEnd_6303577] using wordTrace_append hprefix tailTrace_6303577
  have hstable : (prefixWord ++ tailWord_6303577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303577).length < 2 ^ (prefixWord ++ tailWord_6303577).sum := by decide
  have hdescent : baseEnd_6303577 < baseStart_6303577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303597 : List Nat := [1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 3]
def baseStart_6303597 : Nat := 118140960795 + 6303597 * 2 ^ 59
def prefixEnd_6303597 : Nat := 4983230072969 + 3 ^ 40 * 6303597 * 2
def baseEnd_6303597 : Nat := 3236775113239678881447791

theorem tailTrace_6303597 : CollatzResearch.WordTrace tailWord_6303597 prefixEnd_6303597 3236775113239678881447791 := by
  unfold tailWord_6303597
  simp only [CollatzResearch.WordTrace]
  refine ⟨229911070544152112502701045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153274047029434741668467363 229911070544152112502701045)
  ·
    refine ⟨21554162863514260547128223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229911070544152112502701045 21554162863514260547128223)
    ·
      refine ⟨32331244295271390820692335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21554162863514260547128223 32331244295271390820692335)
      ·
        refine ⟨48496866442907086231038503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32331244295271390820692335 48496866442907086231038503)
        ·
          refine ⟨72745299664360629346557755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48496866442907086231038503 72745299664360629346557755)
          ·
            refine ⟨109117949496540944019836633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72745299664360629346557755 109117949496540944019836633)
            ·
              refine ⟨81838462122405708014877475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109117949496540944019836633 81838462122405708014877475)
              ·
                refine ⟨122757693183608562022316213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81838462122405708014877475 122757693183608562022316213)
                ·
                  refine ⟨11508533735963302689592145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122757693183608562022316213 11508533735963302689592145)
                  ·
                    refine ⟨8631400301972477017194109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11508533735963302689592145 8631400301972477017194109)
                    ·
                      refine ⟨3236775113239678881447791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631400301972477017194109 3236775113239678881447791)
                      ·
                        rfl

theorem cell23_6303597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_6303597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303597 prefixEnd_6303597 := by exact prefixLift 6303597
  have htrace : WordTrace (prefixWord ++ tailWord_6303597) baseStart_6303597 baseEnd_6303597 := by
    simpa [prefixWord, tailWord_6303597, baseEnd_6303597] using wordTrace_append hprefix tailTrace_6303597
  have hstable : (prefixWord ++ tailWord_6303597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303597).length < 2 ^ (prefixWord ++ tailWord_6303597).sum := by decide
  have hdescent : baseEnd_6303597 < baseStart_6303597 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303645 : List Nat := [1, 4, 2, 1, 2, 3, 3, 2, 1, 2, 2]
def baseStart_6303645 : Nat := 118140960795 + 6303645 * 2 ^ 59
def prefixEnd_6303645 : Nat := 4983230072969 + 3 ^ 40 * 6303645 * 2
def baseEnd_6303645 : Nat := 3236799760311094693647571

theorem tailTrace_6303645 : CollatzResearch.WordTrace tailWord_6303645 prefixEnd_6303645 3236799760311094693647571 := by
  unfold tailWord_6303645
  simp only [CollatzResearch.WordTrace]
  refine ⟨229912821247978216700448389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153275214165318811133632259 229912821247978216700448389)
  ·
    refine ⟨43108653983995915631334073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229912821247978216700448389 43108653983995915631334073)
    ·
      refine ⟨32331490487996936723500555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43108653983995915631334073 32331490487996936723500555)
      ·
        refine ⟨48497235731995405085250833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32331490487996936723500555 48497235731995405085250833)
        ·
          refine ⟨36372926798996553813938125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48497235731995405085250833 36372926798996553813938125)
          ·
            refine ⟨13639847549623707680226797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36372926798996553813938125 13639847549623707680226797)
            ·
              refine ⟨5114942831108890380085049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13639847549623707680226797 5114942831108890380085049)
              ·
                refine ⟨3836207123331667785063787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5114942831108890380085049 3836207123331667785063787)
                ·
                  refine ⟨5754310684997501677595681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836207123331667785063787 5754310684997501677595681)
                  ·
                    refine ⟨4315733013748126258196761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5754310684997501677595681 4315733013748126258196761)
                    ·
                      refine ⟨3236799760311094693647571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315733013748126258196761 3236799760311094693647571)
                      ·
                        rfl

theorem cell23_6303645_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 3, 2, 1, 2, 2].length) (baseStart_6303645 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303645 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303645 prefixEnd_6303645 := by exact prefixLift 6303645
  have htrace : WordTrace (prefixWord ++ tailWord_6303645) baseStart_6303645 baseEnd_6303645 := by
    simpa [prefixWord, tailWord_6303645, baseEnd_6303645] using wordTrace_append hprefix tailTrace_6303645
  have hstable : (prefixWord ++ tailWord_6303645).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303645).length < 2 ^ (prefixWord ++ tailWord_6303645).sum := by decide
  have hdescent : baseEnd_6303645 < baseStart_6303645 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303645) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303662 : List Nat := [4, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_6303662 : Nat := 118140960795 + 6303662 * 2 ^ 59
def prefixEnd_6303662 : Nat := 4983230072969 + 3 ^ 40 * 6303662 * 2
def baseEnd_6303662 : Nat := 3236808489482221127134993

theorem tailTrace_6303662 : CollatzResearch.WordTrace tailWord_6303662 prefixEnd_6303662 3236808489482221127134993 := by
  unfold tailWord_6303662
  simp only [CollatzResearch.WordTrace]
  refine ⟨28739180161114578575477155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153275627525944419069211493 28739180161114578575477155)
  ·
    refine ⟨43108770241671867863215733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 28739180161114578575477155 43108770241671867863215733)
    ·
      refine ⟨4041447210156737612176475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 43108770241671867863215733 4041447210156737612176475)
      ·
        refine ⟨6062170815235106418264713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041447210156737612176475 6062170815235106418264713)
        ·
          refine ⟨4546628111426329813698535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6062170815235106418264713 4546628111426329813698535)
          ·
            refine ⟨6819942167139494720547803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4546628111426329813698535 6819942167139494720547803)
            ·
              refine ⟨10229913250709242080821705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6819942167139494720547803 10229913250709242080821705)
              ·
                refine ⟨7672434938031931560616279, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10229913250709242080821705 7672434938031931560616279)
                ·
                  refine ⟨11508652407047897340924419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7672434938031931560616279 11508652407047897340924419)
                  ·
                    refine ⟨17262978610571846011386629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11508652407047897340924419 17262978610571846011386629)
                    ·
                      refine ⟨3236808489482221127134993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17262978610571846011386629 3236808489482221127134993)
                      ·
                        rfl

theorem cell23_6303662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_6303662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303662 prefixEnd_6303662 := by exact prefixLift 6303662
  have htrace : WordTrace (prefixWord ++ tailWord_6303662) baseStart_6303662 baseEnd_6303662 := by
    simpa [prefixWord, tailWord_6303662, baseEnd_6303662] using wordTrace_append hprefix tailTrace_6303662
  have hstable : (prefixWord ++ tailWord_6303662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303662).length < 2 ^ (prefixWord ++ tailWord_6303662).sum := by decide
  have hdescent : baseEnd_6303662 < baseStart_6303662 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303688 : List Nat := [2, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2]
def baseStart_6303688 : Nat := 118140960795 + 6303688 * 2 ^ 59
def prefixEnd_6303688 : Nat := 4983230072969 + 3 ^ 40 * 6303688 * 2
def baseEnd_6303688 : Nat := 3236821839979238025409873

theorem tailTrace_6303688 : CollatzResearch.WordTrace tailWord_6303688 prefixEnd_6303688 3236821839979238025409873 := by
  unfold tailWord_6303688
  simp only [CollatzResearch.WordTrace]
  refine ⟨114957194793411217522131859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153276259724548290029509145 114957194793411217522131859)
  ·
    refine ⟨172435792190116826283197789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114957194793411217522131859 172435792190116826283197789)
    ·
      refine ⟨64663422071293809856199171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172435792190116826283197789 64663422071293809856199171)
      ·
        refine ⟨96995133106940714784298757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64663422071293809856199171 96995133106940714784298757)
        ·
          refine ⟨18186587457551384022056017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 96995133106940714784298757 18186587457551384022056017)
          ·
            refine ⟨13639940593163538016542013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18186587457551384022056017 13639940593163538016542013)
            ·
              refine ⟨5114977722436326756203255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13639940593163538016542013 5114977722436326756203255)
              ·
                refine ⟨7672466583654490134304883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5114977722436326756203255 7672466583654490134304883)
                ·
                  refine ⟨11508699875481735201457325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7672466583654490134304883 11508699875481735201457325)
                  ·
                    refine ⟨4315762453305650700546497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11508699875481735201457325 4315762453305650700546497)
                    ·
                      refine ⟨3236821839979238025409873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315762453305650700546497 3236821839979238025409873)
                      ·
                        rfl

theorem cell23_6303688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 3, 1, 1, 3, 2].length) (baseStart_6303688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303688 prefixEnd_6303688 := by exact prefixLift 6303688
  have htrace : WordTrace (prefixWord ++ tailWord_6303688) baseStart_6303688 baseEnd_6303688 := by
    simpa [prefixWord, tailWord_6303688, baseEnd_6303688] using wordTrace_append hprefix tailTrace_6303688
  have hstable : (prefixWord ++ tailWord_6303688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303688).length < 2 ^ (prefixWord ++ tailWord_6303688).sum := by decide
  have hdescent : baseEnd_6303688 < baseStart_6303688 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303737 : List Nat := [1, 2, 1, 3, 1, 5, 1, 1, 1, 7]
def baseStart_6303737 : Nat := 118140960795 + 6303737 * 2 ^ 59
def prefixEnd_6303737 : Nat := 4983230072969 + 3 ^ 40 * 6303737 * 2
def baseEnd_6303737 : Nat := 1078949000177102777899049

theorem tailTrace_6303737 : CollatzResearch.WordTrace tailWord_6303737 prefixEnd_6303737 1078949000177102777899049 := by
  unfold tailWord_6303737
  simp only [CollatzResearch.WordTrace]
  refine ⟨229916176763644916412797465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153277451175763277608531643 229916176763644916412797465)
  ·
    refine ⟨172437132572733687309598099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229916176763644916412797465 172437132572733687309598099)
    ·
      refine ⟨258655698859100530964397149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172437132572733687309598099 258655698859100530964397149)
      ·
        refine ⟨96995887072162699111648931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 258655698859100530964397149 96995887072162699111648931)
        ·
          refine ⟨145493830608244048667473397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 96995887072162699111648931 145493830608244048667473397)
          ·
            refine ⟨13640046619522879562575631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 145493830608244048667473397 13640046619522879562575631)
            ·
              refine ⟨20460069929284319343863447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13640046619522879562575631 20460069929284319343863447)
              ·
                refine ⟨30690104893926479015795171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20460069929284319343863447 30690104893926479015795171)
                ·
                  refine ⟨46035157340889718523692757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30690104893926479015795171 46035157340889718523692757)
                  ·
                    refine ⟨1078949000177102777899049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 46035157340889718523692757 1078949000177102777899049)
                    ·
                      rfl

theorem cell23_6303737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 5, 1, 1, 1, 7].length) (baseStart_6303737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303737 prefixEnd_6303737 := by exact prefixLift 6303737
  have htrace : WordTrace (prefixWord ++ tailWord_6303737) baseStart_6303737 baseEnd_6303737 := by
    simpa [prefixWord, tailWord_6303737, baseEnd_6303737] using wordTrace_append hprefix tailTrace_6303737
  have hstable : (prefixWord ++ tailWord_6303737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303737).length < 2 ^ (prefixWord ++ tailWord_6303737).sum := by decide
  have hdescent : baseEnd_6303737 < baseStart_6303737 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303794 : List Nat := [3, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3]
def baseStart_6303794 : Nat := 118140960795 + 6303794 * 2 ^ 59
def prefixEnd_6303794 : Nat := 4983230072969 + 3 ^ 40 * 6303794 * 2
def baseEnd_6303794 : Nat := 3236876268928614610684385

theorem tailTrace_6303794 : CollatzResearch.WordTrace tailWord_6303794 prefixEnd_6303794 3236876268928614610684385 := by
  unfold tailWord_6303794
  simp only [CollatzResearch.WordTrace]
  refine ⟨57479563931109603786905609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153278837149625610098414957 57479563931109603786905609)
  ·
    refine ⟨43109672948332202840179207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 57479563931109603786905609 43109672948332202840179207)
    ·
      refine ⟨64664509422498304260268811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 43109672948332202840179207 64664509422498304260268811)
      ·
        refine ⟨96996764133747456390403217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64664509422498304260268811 96996764133747456390403217)
        ·
          refine ⟨72747573100310592292802413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 96996764133747456390403217 72747573100310592292802413)
          ·
            refine ⟨27280339912616472109800905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72747573100310592292802413 27280339912616472109800905)
            ·
              refine ⟨20460254934462354082350679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27280339912616472109800905 20460254934462354082350679)
              ·
                refine ⟨30690382401693531123526019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20460254934462354082350679 30690382401693531123526019)
                ·
                  refine ⟨46035573602540296685289029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30690382401693531123526019 46035573602540296685289029)
                  ·
                    refine ⟨8631670050476305628491693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 46035573602540296685289029 8631670050476305628491693)
                    ·
                      refine ⟨3236876268928614610684385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631670050476305628491693 3236876268928614610684385)
                      ·
                        rfl

theorem cell23_6303794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3].length) (baseStart_6303794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303794 prefixEnd_6303794 := by exact prefixLift 6303794
  have htrace : WordTrace (prefixWord ++ tailWord_6303794) baseStart_6303794 baseEnd_6303794 := by
    simpa [prefixWord, tailWord_6303794, baseEnd_6303794] using wordTrace_append hprefix tailTrace_6303794
  have hstable : (prefixWord ++ tailWord_6303794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303794).length < 2 ^ (prefixWord ++ tailWord_6303794).sum := by decide
  have hdescent : baseEnd_6303794 < baseStart_6303794 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303797 : List Nat := [1, 3, 3, 1, 1, 1, 3, 2, 8]
def baseStart_6303797 : Nat := 118140960795 + 6303797 * 2 ^ 59
def prefixEnd_6303797 : Nat := 4983230072969 + 3 ^ 40 * 6303797 * 2
def baseEnd_6303797 : Nat := 359653089930064233216319

theorem tailTrace_6303797 : CollatzResearch.WordTrace tailWord_6303797 prefixEnd_6303797 359653089930064233216319 := by
  unfold tailWord_6303797
  simp only [CollatzResearch.WordTrace]
  refine ⟨229918365143427546659981645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153278910095618364439987763 229918365143427546659981645)
  ·
    refine ⟨86219386928785329997493117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229918365143427546659981645 86219386928785329997493117)
    ·
      refine ⟨32332270098294498749059919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86219386928785329997493117 32332270098294498749059919)
      ·
        refine ⟨48498405147441748123589879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32332270098294498749059919 48498405147441748123589879)
        ·
          refine ⟨72747607721162622185384819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48498405147441748123589879 72747607721162622185384819)
          ·
            refine ⟨109121411581743933278077229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 72747607721162622185384819 109121411581743933278077229)
            ·
              refine ⟨40920529343153974979278961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 109121411581743933278077229 40920529343153974979278961)
              ·
                refine ⟨30690397007365481234459221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40920529343153974979278961 30690397007365481234459221)
                ·
                  refine ⟨359653089930064233216319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30690397007365481234459221 359653089930064233216319)
                  ·
                    rfl

theorem cell23_6303797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 3, 2, 8].length) (baseStart_6303797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303797 prefixEnd_6303797 := by exact prefixLift 6303797
  have htrace : WordTrace (prefixWord ++ tailWord_6303797) baseStart_6303797 baseEnd_6303797 := by
    simpa [prefixWord, tailWord_6303797, baseEnd_6303797] using wordTrace_append hprefix tailTrace_6303797
  have hstable : (prefixWord ++ tailWord_6303797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303797).length < 2 ^ (prefixWord ++ tailWord_6303797).sum := by decide
  have hdescent : baseEnd_6303797 < baseStart_6303797 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303875 : List Nat := [1, 1, 1, 3, 3, 3, 4, 2, 1, 1, 3]
def baseStart_6303875 : Nat := 118140960795 + 6303875 * 2 ^ 59
def prefixEnd_6303875 : Nat := 4983230072969 + 3 ^ 40 * 6303875 * 2
def baseEnd_6303875 : Nat := 3236917860861628793771513

theorem tailTrace_6303875 : CollatzResearch.WordTrace tailWord_6303875 prefixEnd_6303875 3236917860861628793771513 := by
  unfold tailWord_6303875
  simp only [CollatzResearch.WordTrace]
  refine ⟨229921210037144965981321079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153280806691429977320880719 229921210037144965981321079)
  ·
    refine ⟨344881815055717448971981619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229921210037144965981321079 344881815055717448971981619)
    ·
      refine ⟨517322722583576173457972429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344881815055717448971981619 517322722583576173457972429)
      ·
        refine ⟨193996020968841065046739661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517322722583576173457972429 193996020968841065046739661)
        ·
          refine ⟨72748507863315399392527373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 193996020968841065046739661 72748507863315399392527373)
          ·
            refine ⟨27280690448743274772197765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72748507863315399392527373 27280690448743274772197765)
            ·
              refine ⟨5115129459139364019787081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27280690448743274772197765 5115129459139364019787081)
              ·
                refine ⟨3836347094354523014840311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115129459139364019787081 3836347094354523014840311)
                ·
                  refine ⟨5754520641531784522260467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836347094354523014840311 5754520641531784522260467)
                  ·
                    refine ⟨8631780962297676783390701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5754520641531784522260467 8631780962297676783390701)
                    ·
                      refine ⟨3236917860861628793771513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631780962297676783390701 3236917860861628793771513)
                      ·
                        rfl

theorem cell23_6303875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 4, 2, 1, 1, 3].length) (baseStart_6303875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303875 prefixEnd_6303875 := by exact prefixLift 6303875
  have htrace : WordTrace (prefixWord ++ tailWord_6303875) baseStart_6303875 baseEnd_6303875 := by
    simpa [prefixWord, tailWord_6303875, baseEnd_6303875] using wordTrace_append hprefix tailTrace_6303875
  have hstable : (prefixWord ++ tailWord_6303875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303875).length < 2 ^ (prefixWord ++ tailWord_6303875).sum := by decide
  have hdescent : baseEnd_6303875 < baseStart_6303875 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303897 : List Nat := [1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 7]
def baseStart_6303897 : Nat := 118140960795 + 6303897 * 2 ^ 59
def prefixEnd_6303897 : Nat := 4983230072969 + 3 ^ 40 * 6303897 * 2
def baseEnd_6303897 : Nat := 3236929157436027707696411

theorem tailTrace_6303897 : CollatzResearch.WordTrace tailWord_6303897 prefixEnd_6303897 3236929157436027707696411 := by
  unfold tailWord_6303897
  simp only [CollatzResearch.WordTrace]
  refine ⟨229922012443065263738621945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153281341628710175825747963 229922012443065263738621945)
  ·
    refine ⟨172441509332298947803966459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229922012443065263738621945 172441509332298947803966459)
    ·
      refine ⟨258662263998448421705949689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172441509332298947803966459 258662263998448421705949689)
      ·
        refine ⟨193996697998836316279462267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258662263998448421705949689 193996697998836316279462267)
        ·
          refine ⟨290995046998254474419193401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193996697998836316279462267 290995046998254474419193401)
          ·
            refine ⟨218246285248690855814395051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 290995046998254474419193401 218246285248690855814395051)
            ·
              refine ⟨327369427873036283721592577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218246285248690855814395051 327369427873036283721592577)
              ·
                refine ⟨245527070904777212791194433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327369427873036283721592577 245527070904777212791194433)
                ·
                  refine ⟨184145303178582909593395825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245527070904777212791194433 184145303178582909593395825)
                  ·
                    refine ⟨138108977383937182195046869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 184145303178582909593395825 138108977383937182195046869)
                    ·
                      refine ⟨3236929157436027707696411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 138108977383937182195046869 3236929157436027707696411)
                      ·
                        rfl

theorem cell23_6303897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2, 7].length) (baseStart_6303897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303897 prefixEnd_6303897 := by exact prefixLift 6303897
  have htrace : WordTrace (prefixWord ++ tailWord_6303897) baseStart_6303897 baseEnd_6303897 := by
    simpa [prefixWord, tailWord_6303897, baseEnd_6303897] using wordTrace_append hprefix tailTrace_6303897
  have hstable : (prefixWord ++ tailWord_6303897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303897).length < 2 ^ (prefixWord ++ tailWord_6303897).sum := by decide
  have hdescent : baseEnd_6303897 < baseStart_6303897 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303901 : List Nat := [1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 3]
def baseStart_6303901 : Nat := 118140960795 + 6303901 * 2 ^ 59
def prefixEnd_6303901 : Nat := 4983230072969 + 3 ^ 40 * 6303901 * 2
def baseEnd_6303901 : Nat := 3236931211358645692046393

theorem tailTrace_6303901 : CollatzResearch.WordTrace tailWord_6303901 prefixEnd_6303901 3236931211358645692046393 := by
  unfold tailWord_6303901
  simp only [CollatzResearch.WordTrace]
  refine ⟨229922158335050772421767557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153281438890033848281178371 229922158335050772421767557)
  ·
    refine ⟨43110404687822019829081417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229922158335050772421767557 43110404687822019829081417)
    ·
      refine ⟨32332803515866514871811063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43110404687822019829081417 32332803515866514871811063)
      ·
        refine ⟨48499205273799772307716595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32332803515866514871811063 48499205273799772307716595)
        ·
          refine ⟨72748807910699658461574893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48499205273799772307716595 72748807910699658461574893)
          ·
            refine ⟨27280802966512371923090585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 72748807910699658461574893 27280802966512371923090585)
            ·
              refine ⟨20460602224884278942317939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27280802966512371923090585 20460602224884278942317939)
              ·
                refine ⟨30690903337326418413476909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20460602224884278942317939 30690903337326418413476909)
                ·
                  refine ⟨11509088751497406905053841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30690903337326418413476909 11509088751497406905053841)
                  ·
                    refine ⟨8631816563623055178790381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11509088751497406905053841 8631816563623055178790381)
                    ·
                      refine ⟨3236931211358645692046393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631816563623055178790381 3236931211358645692046393)
                      ·
                        rfl

theorem cell23_6303901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 2, 1, 3, 2, 3].length) (baseStart_6303901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303901 prefixEnd_6303901 := by exact prefixLift 6303901
  have htrace : WordTrace (prefixWord ++ tailWord_6303901) baseStart_6303901 baseEnd_6303901 := by
    simpa [prefixWord, tailWord_6303901, baseEnd_6303901] using wordTrace_append hprefix tailTrace_6303901
  have hstable : (prefixWord ++ tailWord_6303901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303901).length < 2 ^ (prefixWord ++ tailWord_6303901).sum := by decide
  have hdescent : baseEnd_6303901 < baseStart_6303901 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303902 : List Nat := [4, 3, 1, 1, 3, 2, 1, 1, 2, 3, 2]
def baseStart_6303902 : Nat := 118140960795 + 6303902 * 2 ^ 59
def prefixEnd_6303902 : Nat := 4983230072969 + 3 ^ 40 * 6303902 * 2
def baseEnd_6303902 : Nat := 3236931724839300188133889

theorem tailTrace_6303902 : CollatzResearch.WordTrace tailWord_6303902 prefixEnd_6303902 3236931724839300188133889 := by
  unfold tailWord_6303902
  simp only [CollatzResearch.WordTrace]
  refine ⟨28740274351005893699069245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 153281463205364766395035973 28740274351005893699069245)
  ·
    refine ⟨10777602881627210137150967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 28740274351005893699069245 10777602881627210137150967)
    ·
      refine ⟨16166404322440815205726451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10777602881627210137150967 16166404322440815205726451)
      ·
        refine ⟨24249606483661222808589677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16166404322440815205726451 24249606483661222808589677)
        ·
          refine ⟨9093602431372958553221129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24249606483661222808589677 9093602431372958553221129)
          ·
            refine ⟨6820201823529718914915847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9093602431372958553221129 6820201823529718914915847)
            ·
              refine ⟨10230302735294578372373771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820201823529718914915847 10230302735294578372373771)
              ·
                refine ⟨15345454102941867558560657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10230302735294578372373771 15345454102941867558560657)
                ·
                  refine ⟨11509090577206400668920493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15345454102941867558560657 11509090577206400668920493)
                  ·
                    refine ⟨4315908966452400250845185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11509090577206400668920493 4315908966452400250845185)
                    ·
                      refine ⟨3236931724839300188133889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315908966452400250845185 3236931724839300188133889)
                      ·
                        rfl

theorem cell23_6303902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 2, 1, 1, 2, 3, 2].length) (baseStart_6303902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303902 prefixEnd_6303902 := by exact prefixLift 6303902
  have htrace : WordTrace (prefixWord ++ tailWord_6303902) baseStart_6303902 baseEnd_6303902 := by
    simpa [prefixWord, tailWord_6303902, baseEnd_6303902] using wordTrace_append hprefix tailTrace_6303902
  have hstable : (prefixWord ++ tailWord_6303902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303902).length < 2 ^ (prefixWord ++ tailWord_6303902).sum := by decide
  have hdescent : baseEnd_6303902 < baseStart_6303902 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303931 : List Nat := [1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 3]
def baseStart_6303931 : Nat := 118140960795 + 6303931 * 2 ^ 59
def prefixEnd_6303931 : Nat := 4983230072969 + 3 ^ 40 * 6303931 * 2
def baseEnd_6303931 : Nat := 3236946615778280574671255

theorem tailTrace_6303931 : CollatzResearch.WordTrace tailWord_6303931 prefixEnd_6303931 3236946615778280574671255 := by
  unfold tailWord_6303931
  simp only [CollatzResearch.WordTrace]
  refine ⟨229923252524942087545359647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153282168349961391696906431 229923252524942087545359647)
  ·
    refine ⟨344884878787413131318039471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229923252524942087545359647 344884878787413131318039471)
    ·
      refine ⟨517327318181119696977059207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344884878787413131318039471 517327318181119696977059207)
      ·
        refine ⟨775990977271679545465588811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517327318181119696977059207 775990977271679545465588811)
        ·
          refine ⟨1163986465907519318198383217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 775990977271679545465588811 1163986465907519318198383217)
          ·
            refine ⟨872989849430639488648787413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1163986465907519318198383217 872989849430639488648787413)
            ·
              refine ⟨20460699596030613015205955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 872989849430639488648787413 20460699596030613015205955)
              ·
                refine ⟨30691049394045919522808933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20460699596030613015205955 30691049394045919522808933)
                ·
                  refine ⟨5754571761383609910526675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30691049394045919522808933 5754571761383609910526675)
                  ·
                    refine ⟨8631857642075414865790013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5754571761383609910526675 8631857642075414865790013)
                    ·
                      refine ⟨3236946615778280574671255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8631857642075414865790013 3236946615778280574671255)
                      ·
                        rfl

theorem cell23_6303931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 7, 1, 4, 1, 3].length) (baseStart_6303931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303931 prefixEnd_6303931 := by exact prefixLift 6303931
  have htrace : WordTrace (prefixWord ++ tailWord_6303931) baseStart_6303931 baseEnd_6303931 := by
    simpa [prefixWord, tailWord_6303931, baseEnd_6303931] using wordTrace_append hprefix tailTrace_6303931
  have hstable : (prefixWord ++ tailWord_6303931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303931).length < 2 ^ (prefixWord ++ tailWord_6303931).sum := by decide
  have hdescent : baseEnd_6303931 < baseStart_6303931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303941 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 5, 3, 2]
def baseStart_6303941 : Nat := 118140960795 + 6303941 * 2 ^ 59
def prefixEnd_6303941 : Nat := 4983230072969 + 3 ^ 40 * 6303941 * 2
def baseEnd_6303941 : Nat := 3236951750584825535546209

theorem tailTrace_6303941 : CollatzResearch.WordTrace tailWord_6303941 prefixEnd_6303941 3236951750584825535546209 := by
  unfold tailWord_6303941
  simp only [CollatzResearch.WordTrace]
  refine ⟨229923617254905859253223677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153282411503270572835482451 229923617254905859253223677)
  ·
    refine ⟨86221356470589697219958879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229923617254905859253223677 86221356470589697219958879)
    ·
      refine ⟨129332034705884545829938319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86221356470589697219958879 129332034705884545829938319)
      ·
        refine ⟨193998052058826818744907479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129332034705884545829938319 193998052058826818744907479)
        ·
          refine ⟨290997078088240228117361219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 193998052058826818744907479 290997078088240228117361219)
          ·
            refine ⟨436495617132360342176041829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 290997078088240228117361219 436495617132360342176041829)
            ·
              refine ⟨81842928212317564158007843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 436495617132360342176041829 81842928212317564158007843)
              ·
                refine ⟨122764392318476346237011765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 81842928212317564158007843 122764392318476346237011765)
                ·
                  refine ⟨11509161779857157459719853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 122764392318476346237011765 11509161779857157459719853)
                  ·
                    refine ⟨4315935667446434047394945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11509161779857157459719853 4315935667446434047394945)
                    ·
                      refine ⟨3236951750584825535546209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315935667446434047394945 3236951750584825535546209)
                      ·
                        rfl

theorem cell23_6303941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 5, 3, 2].length) (baseStart_6303941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303941 prefixEnd_6303941 := by exact prefixLift 6303941
  have htrace : WordTrace (prefixWord ++ tailWord_6303941) baseStart_6303941 baseEnd_6303941 := by
    simpa [prefixWord, tailWord_6303941, baseEnd_6303941] using wordTrace_append hprefix tailTrace_6303941
  have hstable : (prefixWord ++ tailWord_6303941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303941).length < 2 ^ (prefixWord ++ tailWord_6303941).sum := by decide
  have hdescent : baseEnd_6303941 < baseStart_6303941 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303975 : List Nat := [1, 1, 5, 3, 1, 1, 2, 3, 1, 3, 2]
def baseStart_6303975 : Nat := 118140960795 + 6303975 * 2 ^ 59
def prefixEnd_6303975 : Nat := 4983230072969 + 3 ^ 40 * 6303975 * 2
def baseEnd_6303975 : Nat := 3236969208927078402521053

theorem tailTrace_6303975 : CollatzResearch.WordTrace tailWord_6303975 prefixEnd_6303975 3236969208927078402521053 := by
  unfold tailWord_6303975
  simp only [CollatzResearch.WordTrace]
  refine ⟨229924857336782683059961379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153283238224521788706640919 229924857336782683059961379)
  ·
    refine ⟨344887286005174024589942069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229924857336782683059961379 344887286005174024589942069)
    ·
      refine ⟨32333183062985064805307069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 344887286005174024589942069 32333183062985064805307069)
      ·
        refine ⟨12124943648619399301990151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32333183062985064805307069 12124943648619399301990151)
        ·
          refine ⟨18187415472929098952985227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12124943648619399301990151 18187415472929098952985227)
          ·
            refine ⟨27281123209393648429477841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18187415472929098952985227 27281123209393648429477841)
            ·
              refine ⟨20460842407045236322108381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27281123209393648429477841 20460842407045236322108381)
              ·
                refine ⟨7672815902641963620790643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20460842407045236322108381 7672815902641963620790643)
                ·
                  refine ⟨11509223853962945431185965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7672815902641963620790643 11509223853962945431185965)
                  ·
                    refine ⟨4315958945236104536694737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11509223853962945431185965 4315958945236104536694737)
                    ·
                      refine ⟨3236969208927078402521053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4315958945236104536694737 3236969208927078402521053)
                      ·
                        rfl

theorem cell23_6303975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 2, 3, 1, 3, 2].length) (baseStart_6303975 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303975 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303975 prefixEnd_6303975 := by exact prefixLift 6303975
  have htrace : WordTrace (prefixWord ++ tailWord_6303975) baseStart_6303975 baseEnd_6303975 := by
    simpa [prefixWord, tailWord_6303975, baseEnd_6303975] using wordTrace_append hprefix tailTrace_6303975
  have hstable : (prefixWord ++ tailWord_6303975).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303975).length < 2 ^ (prefixWord ++ tailWord_6303975).sum := by decide
  have hdescent : baseEnd_6303975 < baseStart_6303975 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6303984 : List Nat := [2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4]
def baseStart_6303984 : Nat := 118140960795 + 6303984 * 2 ^ 59
def prefixEnd_6303984 : Nat := 4983230072969 + 3 ^ 40 * 6303984 * 2
def baseEnd_6303984 : Nat := 3236973830252968867308511

theorem tailTrace_6303984 : CollatzResearch.WordTrace tailWord_6303984 prefixEnd_6303984 3236973830252968867308511 := by
  unfold tailWord_6303984
  simp only [CollatzResearch.WordTrace]
  refine ⟨114962592796875038798519503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153283457062500051731359337 114962592796875038798519503)
  ·
    refine ⟨172443889195312558197779255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114962592796875038798519503 172443889195312558197779255)
    ·
      refine ⟨258665833792968837296668883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172443889195312558197779255 258665833792968837296668883)
      ·
        refine ⟨387998750689453255945003325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258665833792968837296668883 387998750689453255945003325)
        ·
          refine ⟨145499531508544970979376247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 387998750689453255945003325 145499531508544970979376247)
          ·
            refine ⟨218249297262817456469064371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145499531508544970979376247 218249297262817456469064371)
            ·
              refine ⟨327373945894226184703596557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 218249297262817456469064371 327373945894226184703596557)
              ·
                refine ⟨122765229710334819263848709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 327373945894226184703596557 122765229710334819263848709)
                ·
                  refine ⟨23018480570687778611971633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 122765229710334819263848709 23018480570687778611971633)
                  ·
                    refine ⟨17263860428015833958978725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 23018480570687778611971633 17263860428015833958978725)
                    ·
                      refine ⟨3236973830252968867308511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17263860428015833958978725 3236973830252968867308511)
                      ·
                        rfl

theorem cell23_6303984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 3, 4, 2, 4].length) (baseStart_6303984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6303984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6303984 prefixEnd_6303984 := by exact prefixLift 6303984
  have htrace : WordTrace (prefixWord ++ tailWord_6303984) baseStart_6303984 baseEnd_6303984 := by
    simpa [prefixWord, tailWord_6303984, baseEnd_6303984] using wordTrace_append hprefix tailTrace_6303984
  have hstable : (prefixWord ++ tailWord_6303984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6303984).length < 2 ^ (prefixWord ++ tailWord_6303984).sum := by decide
  have hdescent : baseEnd_6303984 < baseStart_6303984 := by decide
  rcases family_descends (prefixWord ++ tailWord_6303984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304101 : List Nat := [1, 3, 1, 3, 1, 4, 1, 1, 8]
def baseStart_6304101 : Nat := 118140960795 + 6304101 * 2 ^ 59
def prefixEnd_6304101 : Nat := 4983230072969 + 3 ^ 40 * 6304101 * 2
def baseEnd_6304101 : Nat := 359670434165504989949497

theorem tailTrace_6304101 : CollatzResearch.WordTrace tailWord_6304101 prefixEnd_6304101 359670434165504989949497 := by
  unfold tailWord_6304101
  simp only [CollatzResearch.WordTrace]
  refine ⟨229929452934326206579048157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153286301956217471052698771 229929452934326206579048157)
  ·
    refine ⟨86223544850372327467143059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229929452934326206579048157 86223544850372327467143059)
    ·
      refine ⟨129335317275558491200714589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86223544850372327467143059 129335317275558491200714589)
      ·
        refine ⟨48500743978334434200267971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129335317275558491200714589 48500743978334434200267971)
        ·
          refine ⟨72751115967501651300401957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48500743978334434200267971 72751115967501651300401957)
          ·
            refine ⟨13640834243906559618825367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72751115967501651300401957 13640834243906559618825367)
            ·
              refine ⟨20461251365859839428238051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13640834243906559618825367 20461251365859839428238051)
              ·
                refine ⟨30691877048789759142357077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20461251365859839428238051 30691877048789759142357077)
                ·
                  refine ⟨359670434165504989949497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 30691877048789759142357077 359670434165504989949497)
                  ·
                    rfl

theorem cell23_6304101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 4, 1, 1, 8].length) (baseStart_6304101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304101 prefixEnd_6304101 := by exact prefixLift 6304101
  have htrace : WordTrace (prefixWord ++ tailWord_6304101) baseStart_6304101 baseEnd_6304101 := by
    simpa [prefixWord, tailWord_6304101, baseEnd_6304101] using wordTrace_append hprefix tailTrace_6304101
  have hstable : (prefixWord ++ tailWord_6304101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304101).length < 2 ^ (prefixWord ++ tailWord_6304101).sum := by decide
  have hdescent : baseEnd_6304101 < baseStart_6304101 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304185 : List Nat := [1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 4]
def baseStart_6304185 : Nat := 118140960795 + 6304185 * 2 ^ 59
def prefixEnd_6304185 : Nat := 4983230072969 + 3 ^ 40 * 6304185 * 2
def baseEnd_6304185 : Nat := 3237077039864522580895087

theorem tailTrace_6304185 : CollatzResearch.WordTrace tailWord_6304185 prefixEnd_6304185 3237077039864522580895087 := by
  unfold tailWord_6304185
  simp only [CollatzResearch.WordTrace]
  refine ⟨229932516666021888925106009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153288344444014592616737339 229932516666021888925106009)
  ·
    refine ⟨172449387499516416693829507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229932516666021888925106009 172449387499516416693829507)
    ·
      refine ⟨258674081249274625040744261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172449387499516416693829507 258674081249274625040744261)
      ·
        refine ⟨48501390234238992195139549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 258674081249274625040744261 48501390234238992195139549)
        ·
          refine ⟨18188021337839622073177331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48501390234238992195139549 18188021337839622073177331)
          ·
            refine ⟨27282032006759433109765997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18188021337839622073177331 27282032006759433109765997)
            ·
              refine ⟨10230762002534787416162249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27282032006759433109765997 10230762002534787416162249)
              ·
                refine ⟨7673071501901090562121687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10230762002534787416162249 7673071501901090562121687)
                ·
                  refine ⟨11509607252851635843182531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673071501901090562121687 11509607252851635843182531)
                  ·
                    refine ⟨17264410879277453764773797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11509607252851635843182531 17264410879277453764773797)
                    ·
                      refine ⟨3237077039864522580895087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17264410879277453764773797 3237077039864522580895087)
                      ·
                        rfl

theorem cell23_6304185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 3, 2, 1, 1, 4].length) (baseStart_6304185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304185 prefixEnd_6304185 := by exact prefixLift 6304185
  have htrace : WordTrace (prefixWord ++ tailWord_6304185) baseStart_6304185 baseEnd_6304185 := by
    simpa [prefixWord, tailWord_6304185, baseEnd_6304185] using wordTrace_append hprefix tailTrace_6304185
  have hstable : (prefixWord ++ tailWord_6304185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304185).length < 2 ^ (prefixWord ++ tailWord_6304185).sum := by decide
  have hdescent : baseEnd_6304185 < baseStart_6304185 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304212 : List Nat := [2, 4, 1, 2, 2, 2, 2, 2, 2, 4]
def baseStart_6304212 : Nat := 118140960795 + 6304212 * 2 ^ 59
def prefixEnd_6304212 : Nat := 4983230072969 + 3 ^ 40 * 6304212 * 2
def baseEnd_6304212 : Nat := 1079030301280731325085821

theorem tailTrace_6304212 : CollatzResearch.WordTrace tailWord_6304212 prefixEnd_6304212 1079030301280731325085821 := by
  unfold tailWord_6304212
  simp only [CollatzResearch.WordTrace]
  refine ⟨114966750718462036268169445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153289000957949381690892593 114966750718462036268169445)
  ·
    refine ⟨21556265759711631800281771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 114966750718462036268169445 21556265759711631800281771)
    ·
      refine ⟨32334398639567447700422657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21556265759711631800281771 32334398639567447700422657)
      ·
        refine ⟨24250798979675585775316993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32334398639567447700422657 24250798979675585775316993)
        ·
          refine ⟨18188099234756689331487745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24250798979675585775316993 18188099234756689331487745)
          ·
            refine ⟨13641074426067516998615809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18188099234756689331487745 13641074426067516998615809)
            ·
              refine ⟨10230805819550637748961857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13641074426067516998615809 10230805819550637748961857)
              ·
                refine ⟨7673104364662978311721393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10230805819550637748961857 7673104364662978311721393)
                ·
                  refine ⟨5754828273497233733791045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673104364662978311721393 5754828273497233733791045)
                  ·
                    refine ⟨1079030301280731325085821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5754828273497233733791045 1079030301280731325085821)
                    ·
                      rfl

theorem cell23_6304212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 2, 2, 2, 2, 4].length) (baseStart_6304212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304212 prefixEnd_6304212 := by exact prefixLift 6304212
  have htrace : WordTrace (prefixWord ++ tailWord_6304212) baseStart_6304212 baseEnd_6304212 := by
    simpa [prefixWord, tailWord_6304212, baseEnd_6304212] using wordTrace_append hprefix tailTrace_6304212
  have hstable : (prefixWord ++ tailWord_6304212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304212).length < 2 ^ (prefixWord ++ tailWord_6304212).sum := by decide
  have hdescent : baseEnd_6304212 < baseStart_6304212 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304218 : List Nat := [3, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3]
def baseStart_6304218 : Nat := 118140960795 + 6304218 * 2 ^ 59
def prefixEnd_6304218 : Nat := 4983230072969 + 3 ^ 40 * 6304218 * 2
def baseEnd_6304218 : Nat := 3237093984726120951782435

theorem tailTrace_6304218 : CollatzResearch.WordTrace tailWord_6304218 prefixEnd_6304218 3237093984726120951782435 := by
  unfold tailWord_6304218
  simp only [CollatzResearch.WordTrace]
  refine ⟨57483430068725583890264327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153289146849934890374038205 57483430068725583890264327)
  ·
    refine ⟨86225145103088375835396491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57483430068725583890264327 86225145103088375835396491)
    ·
      refine ⟨129337717654632563753094737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86225145103088375835396491 129337717654632563753094737)
      ·
        refine ⟨97003288240974422814821053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129337717654632563753094737 97003288240974422814821053)
        ·
          refine ⟨36376233090365408555557895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97003288240974422814821053 36376233090365408555557895)
          ·
            refine ⟨54564349635548112833336843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36376233090365408555557895 54564349635548112833336843)
            ·
              refine ⟨81846524453322169250005265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 54564349635548112833336843 81846524453322169250005265)
              ·
                refine ⟨61384893339991626937503949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 81846524453322169250005265 61384893339991626937503949)
                ·
                  refine ⟨23019335002496860101563981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 61384893339991626937503949 23019335002496860101563981)
                  ·
                    refine ⟨8632250625936322538086493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23019335002496860101563981 8632250625936322538086493)
                    ·
                      refine ⟨3237093984726120951782435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632250625936322538086493 3237093984726120951782435)
                      ·
                        rfl

theorem cell23_6304218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 2, 3, 3, 3].length) (baseStart_6304218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304218 prefixEnd_6304218 := by exact prefixLift 6304218
  have htrace : WordTrace (prefixWord ++ tailWord_6304218) baseStart_6304218 baseEnd_6304218 := by
    simpa [prefixWord, tailWord_6304218, baseEnd_6304218] using wordTrace_append hprefix tailTrace_6304218
  have hstable : (prefixWord ++ tailWord_6304218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304218).length < 2 ^ (prefixWord ++ tailWord_6304218).sum := by decide
  have hdescent : baseEnd_6304218 < baseStart_6304218 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304235 : List Nat := [1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 3]
def baseStart_6304235 : Nat := 118140960795 + 6304235 * 2 ^ 59
def prefixEnd_6304235 : Nat := 4983230072969 + 3 ^ 40 * 6304235 * 2
def baseEnd_6304235 : Nat := 3237102713897247385269857

theorem tailTrace_6304235 : CollatzResearch.WordTrace tailWord_6304235 prefixEnd_6304235 3237102713897247385269857 := by
  unfold tailWord_6304235
  simp only [CollatzResearch.WordTrace]
  refine ⟨229934340315840747464426159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153289560210560498309617439 229934340315840747464426159)
  ·
    refine ⟨344901510473761121196639239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229934340315840747464426159 344901510473761121196639239)
    ·
      refine ⟨517352265710641681794958859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344901510473761121196639239 517352265710641681794958859)
      ·
        refine ⟨776028398565962522692438289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517352265710641681794958859 776028398565962522692438289)
        ·
          refine ⟨582021298924471892019328717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 776028398565962522692438289 582021298924471892019328717)
          ·
            refine ⟨218257987096676959507248269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 582021298924471892019328717 218257987096676959507248269)
            ·
              refine ⟨81846745161253859815218101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 218257987096676959507248269 81846745161253859815218101)
              ·
                refine ⟨7673132358867549357676697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 81846745161253859815218101 7673132358867549357676697)
                ·
                  refine ⟨5754849269150662018257523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7673132358867549357676697 5754849269150662018257523)
                  ·
                    refine ⟨8632273903725993027386285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5754849269150662018257523 8632273903725993027386285)
                    ·
                      refine ⟨3237102713897247385269857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632273903725993027386285 3237102713897247385269857)
                      ·
                        rfl

theorem cell23_6304235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 3, 5, 2, 1, 3].length) (baseStart_6304235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304235 prefixEnd_6304235 := by exact prefixLift 6304235
  have htrace : WordTrace (prefixWord ++ tailWord_6304235) baseStart_6304235 baseEnd_6304235 := by
    simpa [prefixWord, tailWord_6304235, baseEnd_6304235] using wordTrace_append hprefix tailTrace_6304235
  have hstable : (prefixWord ++ tailWord_6304235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304235).length < 2 ^ (prefixWord ++ tailWord_6304235).sum := by decide
  have hdescent : baseEnd_6304235 < baseStart_6304235 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304251 : List Nat := [1, 1, 1, 1, 1, 3, 2, 1, 6, 6]
def baseStart_6304251 : Nat := 118140960795 + 6304251 * 2 ^ 59
def prefixEnd_6304251 : Nat := 4983230072969 + 3 ^ 40 * 6304251 * 2
def baseEnd_6304251 : Nat := 1079036976529239774223261

theorem tailTrace_6304251 : CollatzResearch.WordTrace tailWord_6304251 prefixEnd_6304251 1079036976529239774223261 := by
  unfold tailWord_6304251
  simp only [CollatzResearch.WordTrace]
  refine ⟨229934923883782782197008607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153289949255855188131339071 229934923883782782197008607)
  ·
    refine ⟨344902385825674173295512911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229934923883782782197008607 344902385825674173295512911)
    ·
      refine ⟨517353578738511259943269367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344902385825674173295512911 517353578738511259943269367)
      ·
        refine ⟨776030368107766889914904051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 517353578738511259943269367 776030368107766889914904051)
        ·
          refine ⟨1164045552161650334872356077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 776030368107766889914904051 1164045552161650334872356077)
          ·
            refine ⟨436517082060618875577133529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1164045552161650334872356077 436517082060618875577133529)
            ·
              refine ⟨327387811545464156682850147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436517082060618875577133529 327387811545464156682850147)
              ·
                refine ⟨491081717318196235024275221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 327387811545464156682850147 491081717318196235024275221)
                ·
                  refine ⟨23019455499290448516762901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 491081717318196235024275221 23019455499290448516762901)
                  ·
                    refine ⟨1079036976529239774223261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23019455499290448516762901 1079036976529239774223261)
                    ·
                      rfl

theorem cell23_6304251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_6304251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304251 prefixEnd_6304251 := by exact prefixLift 6304251
  have htrace : WordTrace (prefixWord ++ tailWord_6304251) baseStart_6304251 baseEnd_6304251 := by
    simpa [prefixWord, tailWord_6304251, baseEnd_6304251] using wordTrace_append hprefix tailTrace_6304251
  have hstable : (prefixWord ++ tailWord_6304251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304251).length < 2 ^ (prefixWord ++ tailWord_6304251).sum := by decide
  have hdescent : baseEnd_6304251 < baseStart_6304251 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304268 : List Nat := [2, 2, 1, 2, 4, 1, 1, 2, 2, 6]
def baseStart_6304268 : Nat := 118140960795 + 6304268 * 2 ^ 59
def prefixEnd_6304268 : Nat := 4983230072969 + 3 ^ 40 * 6304268 * 2
def baseEnd_6304268 : Nat := 1079039886252948585385735

theorem tailTrace_6304268 : CollatzResearch.WordTrace tailWord_6304268 prefixEnd_6304268 1079039886252948585385735 := by
  unfold tailWord_6304268
  simp only [CollatzResearch.WordTrace]
  refine ⟨114967771962360597050188729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153290362616480796066918305 114967771962360597050188729)
  ·
    refine ⟨86225828971770447787641547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114967771962360597050188729 86225828971770447787641547)
    ·
      refine ⟨129338743457655671681462321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86225828971770447787641547 129338743457655671681462321)
      ·
        refine ⟨97004057593241753761096741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129338743457655671681462321 97004057593241753761096741)
        ·
          refine ⟨18188260798732828830205639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97004057593241753761096741 18188260798732828830205639)
          ·
            refine ⟨27282391198099243245308459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18188260798732828830205639 27282391198099243245308459)
            ·
              refine ⟨40923586797148864867962689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27282391198099243245308459 40923586797148864867962689)
              ·
                refine ⟨30692690097861648650972017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40923586797148864867962689 30692690097861648650972017)
                ·
                  refine ⟨23019517573396236488229013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30692690097861648650972017 23019517573396236488229013)
                  ·
                    refine ⟨1079039886252948585385735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23019517573396236488229013 1079039886252948585385735)
                    ·
                      rfl

theorem cell23_6304268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 1, 2, 2, 6].length) (baseStart_6304268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304268 prefixEnd_6304268 := by exact prefixLift 6304268
  have htrace : WordTrace (prefixWord ++ tailWord_6304268) baseStart_6304268 baseEnd_6304268 := by
    simpa [prefixWord, tailWord_6304268, baseEnd_6304268] using wordTrace_append hprefix tailTrace_6304268
  have hstable : (prefixWord ++ tailWord_6304268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304268).length < 2 ^ (prefixWord ++ tailWord_6304268).sum := by decide
  have hdescent : baseEnd_6304268 < baseStart_6304268 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304271 : List Nat := [1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6]
def baseStart_6304271 : Nat := 118140960795 + 6304271 * 2 ^ 59
def prefixEnd_6304271 : Nat := 4983230072969 + 3 ^ 40 * 6304271 * 2
def baseEnd_6304271 : Nat := 3237121199200809244419691

theorem tailTrace_6304271 : CollatzResearch.WordTrace tailWord_6304271 prefixEnd_6304271 3237121199200809244419691 := by
  unfold tailWord_6304271
  simp only [CollatzResearch.WordTrace]
  refine ⟨229935653343710325612736667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153290435562473550408491111 229935653343710325612736667)
  ·
    refine ⟨344903480015565488419105001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229935653343710325612736667 344903480015565488419105001)
    ·
      refine ⟨258677610011674116314328751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344903480015565488419105001 258677610011674116314328751)
      ·
        refine ⟨388016415017511174471493127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258677610011674116314328751 388016415017511174471493127)
        ·
          refine ⟨582024622526266761707239691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 388016415017511174471493127 582024622526266761707239691)
          ·
            refine ⟨873036933789400142560859537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 582024622526266761707239691 873036933789400142560859537)
            ·
              refine ⟨654777700342050106920644653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 873036933789400142560859537 654777700342050106920644653)
              ·
                refine ⟨245541637628268790095241745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 654777700342050106920644653 245541637628268790095241745)
                ·
                  refine ⟨184156228221201592571431309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 245541637628268790095241745 184156228221201592571431309)
                  ·
                    refine ⟨69058585582950597214286741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 184156228221201592571431309 69058585582950597214286741)
                    ·
                      refine ⟨3237121199200809244419691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 69058585582950597214286741 3237121199200809244419691)
                      ·
                        rfl

theorem cell23_6304271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 3, 2, 3, 6].length) (baseStart_6304271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304271 prefixEnd_6304271 := by exact prefixLift 6304271
  have htrace : WordTrace (prefixWord ++ tailWord_6304271) baseStart_6304271 baseEnd_6304271 := by
    simpa [prefixWord, tailWord_6304271, baseEnd_6304271] using wordTrace_append hprefix tailTrace_6304271
  have hstable : (prefixWord ++ tailWord_6304271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304271).length < 2 ^ (prefixWord ++ tailWord_6304271).sum := by decide
  have hdescent : baseEnd_6304271 < baseStart_6304271 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304281 : List Nat := [1, 2, 1, 2, 1, 1, 2, 2, 11]
def baseStart_6304281 : Nat := 118140960795 + 6304281 * 2 ^ 59
def prefixEnd_6304281 : Nat := 4983230072969 + 3 ^ 40 * 6304281 * 2
def baseEnd_6304281 : Nat := 359680703778594911699405

theorem tailTrace_6304281 : CollatzResearch.WordTrace tailWord_6304281 prefixEnd_6304281 359680703778594911699405 := by
  unfold tailWord_6304281
  simp only [CollatzResearch.WordTrace]
  refine ⟨229936018073674097320600697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153290678715782731547067131 229936018073674097320600697)
  ·
    refine ⟨172452013555255572990450523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229936018073674097320600697 172452013555255572990450523)
    ·
      refine ⟨258678020332883359485675785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172452013555255572990450523 258678020332883359485675785)
      ·
        refine ⟨194008515249662519614256839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 258678020332883359485675785 194008515249662519614256839)
        ·
          refine ⟨291012772874493779421385259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194008515249662519614256839 291012772874493779421385259)
          ·
            refine ⟨436519159311740669132077889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291012772874493779421385259 436519159311740669132077889)
            ·
              refine ⟨327389369483805501849058417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 436519159311740669132077889 327389369483805501849058417)
              ·
                refine ⟨245542027112854126386793813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 327389369483805501849058417 245542027112854126386793813)
                ·
                  refine ⟨359680703778594911699405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 245542027112854126386793813 359680703778594911699405)
                  ·
                    rfl

theorem cell23_6304281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 2, 11].length) (baseStart_6304281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304281 prefixEnd_6304281 := by exact prefixLift 6304281
  have htrace : WordTrace (prefixWord ++ tailWord_6304281) baseStart_6304281 baseEnd_6304281 := by
    simpa [prefixWord, tailWord_6304281, baseEnd_6304281] using wordTrace_append hprefix tailTrace_6304281
  have hstable : (prefixWord ++ tailWord_6304281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304281).length < 2 ^ (prefixWord ++ tailWord_6304281).sum := by decide
  have hdescent : baseEnd_6304281 < baseStart_6304281 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304326 : List Nat := [6, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_6304326 : Nat := 118140960795 + 6304326 * 2 ^ 59
def prefixEnd_6304326 : Nat := 4983230072969 + 3 ^ 40 * 6304326 * 2
def baseEnd_6304326 : Nat := 3237149440636806529231939

theorem tailTrace_6304326 : CollatzResearch.WordTrace tailWord_6304326 prefixEnd_6304326 3237149440636806529231939 := by
  unfold tailWord_6304326
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185551854953470937687151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 153291772905674046670659221 7185551854953470937687151)
  ·
    refine ⟨10778327782430206406530727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185551854953470937687151 10778327782430206406530727)
    ·
      refine ⟨16167491673645309609796091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778327782430206406530727 16167491673645309609796091)
      ·
        refine ⟨24251237510467964414694137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16167491673645309609796091 24251237510467964414694137)
        ·
          refine ⟨18188428132850973311020603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24251237510467964414694137 18188428132850973311020603)
          ·
            refine ⟨27282642199276459966530905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18188428132850973311020603 27282642199276459966530905)
            ·
              refine ⟨20461981649457344974898179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27282642199276459966530905 20461981649457344974898179)
              ·
                refine ⟨30692972474186017462347269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20461981649457344974898179 30692972474186017462347269)
                ·
                  refine ⟨5754932338909878274190113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 30692972474186017462347269 5754932338909878274190113)
                  ·
                    refine ⟨4316199254182408705642585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5754932338909878274190113 4316199254182408705642585)
                    ·
                      refine ⟨3237149440636806529231939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316199254182408705642585 3237149440636806529231939)
                      ·
                        rfl

theorem cell23_6304326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_6304326 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304326 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304326 prefixEnd_6304326 := by exact prefixLift 6304326
  have htrace : WordTrace (prefixWord ++ tailWord_6304326) baseStart_6304326 baseEnd_6304326 := by
    simpa [prefixWord, tailWord_6304326, baseEnd_6304326] using wordTrace_append hprefix tailTrace_6304326
  have hstable : (prefixWord ++ tailWord_6304326).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304326).length < 2 ^ (prefixWord ++ tailWord_6304326).sum := by decide
  have hdescent : baseEnd_6304326 < baseStart_6304326 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304332 : List Nat := [2, 2, 1, 3, 1, 2, 5, 2, 5]
def baseStart_6304332 : Nat := 118140960795 + 6304332 * 2 ^ 59
def prefixEnd_6304332 : Nat := 4983230072969 + 3 ^ 40 * 6304332 * 2
def baseEnd_6304332 : Nat := 359683613502303722861879

theorem tailTrace_6304332 : CollatzResearch.WordTrace tailWord_6304332 prefixEnd_6304332 359683613502303722861879 := by
  unfold tailWord_6304332
  simp only [CollatzResearch.WordTrace]
  refine ⟨114968939098244666515353625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153291918797659555353804833 114968939098244666515353625)
  ·
    refine ⟨86226704323683499886515219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114968939098244666515353625 86226704323683499886515219)
    ·
      refine ⟨129340056485525249829772829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86226704323683499886515219 129340056485525249829772829)
      ·
        refine ⟨48502521182071968686164811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 129340056485525249829772829 48502521182071968686164811)
        ·
          refine ⟨72753781773107953029247217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48502521182071968686164811 72753781773107953029247217)
          ·
            refine ⟨54565336329830964771935413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72753781773107953029247217 54565336329830964771935413)
            ·
              refine ⟨5115500280921652947368945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 54565336329830964771935413 5115500280921652947368945)
              ·
                refine ⟨3836625210691239710526709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115500280921652947368945 3836625210691239710526709)
                ·
                  refine ⟨359683613502303722861879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3836625210691239710526709 359683613502303722861879)
                  ·
                    rfl

theorem cell23_6304332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 5, 2, 5].length) (baseStart_6304332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304332 prefixEnd_6304332 := by exact prefixLift 6304332
  have htrace : WordTrace (prefixWord ++ tailWord_6304332) baseStart_6304332 baseEnd_6304332 := by
    simpa [prefixWord, tailWord_6304332, baseEnd_6304332] using wordTrace_append hprefix tailTrace_6304332
  have hstable : (prefixWord ++ tailWord_6304332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304332).length < 2 ^ (prefixWord ++ tailWord_6304332).sum := by decide
  have hdescent : baseEnd_6304332 < baseStart_6304332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304378 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4]
def baseStart_6304378 : Nat := 118140960795 + 6304378 * 2 ^ 59
def prefixEnd_6304378 : Nat := 4983230072969 + 3 ^ 40 * 6304378 * 2
def baseEnd_6304378 : Nat := 3237176141630840325781699

theorem tailTrace_6304378 : CollatzResearch.WordTrace tailWord_6304378 prefixEnd_6304378 3237176141630840325781699 := by
  unfold tailWord_6304378
  simp only [CollatzResearch.WordTrace]
  refine ⟨57484888988580670721720447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153293037302881788591254525 57484888988580670721720447)
  ·
    refine ⟨86227333482871006082580671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57484888988580670721720447 86227333482871006082580671)
    ·
      refine ⟨129341000224306509123871007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86227333482871006082580671 129341000224306509123871007)
      ·
        refine ⟨194011500336459763685806511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129341000224306509123871007 194011500336459763685806511)
        ·
          refine ⟨291017250504689645528709767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194011500336459763685806511 291017250504689645528709767)
          ·
            refine ⟨436525875757034468293064651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 291017250504689645528709767 436525875757034468293064651)
            ·
              refine ⟨654788813635551702439596977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 436525875757034468293064651 654788813635551702439596977)
              ·
                refine ⟨491091610226663776829697733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 654788813635551702439596977 491091610226663776829697733)
                ·
                  refine ⟨92079676917499458155568325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 491091610226663776829697733 92079676917499458155568325)
                  ·
                    refine ⟨17264939422031148404169061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 92079676917499458155568325 17264939422031148404169061)
                    ·
                      refine ⟨3237176141630840325781699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17264939422031148404169061 3237176141630840325781699)
                      ·
                        rfl

theorem cell23_6304378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 4, 4, 4].length) (baseStart_6304378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304378 prefixEnd_6304378 := by exact prefixLift 6304378
  have htrace : WordTrace (prefixWord ++ tailWord_6304378) baseStart_6304378 baseEnd_6304378 := by
    simpa [prefixWord, tailWord_6304378, baseEnd_6304378] using wordTrace_append hprefix tailTrace_6304378
  have hstable : (prefixWord ++ tailWord_6304378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304378).length < 2 ^ (prefixWord ++ tailWord_6304378).sum := by decide
  have hdescent : baseEnd_6304378 < baseStart_6304378 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304439 : List Nat := [1, 1, 3, 1, 7, 1, 1, 2, 6]
def baseStart_6304439 : Nat := 118140960795 + 6304439 * 2 ^ 59
def prefixEnd_6304439 : Nat := 4983230072969 + 3 ^ 40 * 6304439 * 2
def baseEnd_6304439 : Nat := 359689718216751620790991

theorem tailTrace_6304439 : CollatzResearch.WordTrace tailWord_6304439 prefixEnd_6304439 359689718216751620790991 := by
  unfold tailWord_6304439
  simp only [CollatzResearch.WordTrace]
  refine ⟨229941780807101690304852371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153294520538067793536568247 229941780807101690304852371)
  ·
    refine ⟨344912671210652535457278557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229941780807101690304852371 344912671210652535457278557)
    ·
      refine ⟨129342251703994700796479459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 344912671210652535457278557 129342251703994700796479459)
      ·
        refine ⟨194013377555992051194719189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129342251703994700796479459 194013377555992051194719189)
        ·
          refine ⟨4547188536468563699876231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 194013377555992051194719189 4547188536468563699876231)
          ·
            refine ⟨6820782804702845549814347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547188536468563699876231 6820782804702845549814347)
            ·
              refine ⟨10231174207054268324721521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820782804702845549814347 10231174207054268324721521)
              ·
                refine ⟨7673380655290701243541141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10231174207054268324721521 7673380655290701243541141)
                ·
                  refine ⟨359689718216751620790991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7673380655290701243541141 359689718216751620790991)
                  ·
                    rfl

theorem cell23_6304439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 2, 6].length) (baseStart_6304439 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304439 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304439 prefixEnd_6304439 := by exact prefixLift 6304439
  have htrace : WordTrace (prefixWord ++ tailWord_6304439) baseStart_6304439 baseEnd_6304439 := by
    simpa [prefixWord, tailWord_6304439, baseEnd_6304439] using wordTrace_append hprefix tailTrace_6304439
  have hstable : (prefixWord ++ tailWord_6304439).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304439).length < 2 ^ (prefixWord ++ tailWord_6304439).sum := by decide
  have hdescent : baseEnd_6304439 < baseStart_6304439 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304442 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2]
def baseStart_6304442 : Nat := 118140960795 + 6304442 * 2 ^ 59
def prefixEnd_6304442 : Nat := 4983230072969 + 3 ^ 40 * 6304442 * 2
def baseEnd_6304442 : Nat := 3237209004392728075381405

theorem tailTrace_6304442 : CollatzResearch.WordTrace tailWord_6304442 prefixEnd_6304442 3237209004392728075381405 := by
  unfold tailWord_6304442
  simp only [CollatzResearch.WordTrace]
  refine ⟨57485472556522705454302895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153294593484060547878141053 57485472556522705454302895)
  ·
    refine ⟨86228208834784058181454343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57485472556522705454302895 86228208834784058181454343)
    ·
      refine ⟨129342313252176087272181515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86228208834784058181454343 129342313252176087272181515)
      ·
        refine ⟨194013469878264130908272273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129342313252176087272181515 194013469878264130908272273)
        ·
          refine ⟨145510102408698098181204205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 194013469878264130908272273 145510102408698098181204205)
          ·
            refine ⟨54566288403261786817951577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 145510102408698098181204205 54566288403261786817951577)
            ·
              refine ⟨40924716302446340113463683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54566288403261786817951577 40924716302446340113463683)
              ·
                refine ⟨61387074453669510170195525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40924716302446340113463683 61387074453669510170195525)
                ·
                  refine ⟨11510076460063033156911661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 61387074453669510170195525 11510076460063033156911661)
                  ·
                    refine ⟨4316278672523637433841873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 11510076460063033156911661 4316278672523637433841873)
                    ·
                      refine ⟨3237209004392728075381405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316278672523637433841873 3237209004392728075381405)
                      ·
                        rfl

theorem cell23_6304442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 4, 3, 2].length) (baseStart_6304442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304442 prefixEnd_6304442 := by exact prefixLift 6304442
  have htrace : WordTrace (prefixWord ++ tailWord_6304442) baseStart_6304442 baseEnd_6304442 := by
    simpa [prefixWord, tailWord_6304442, baseEnd_6304442] using wordTrace_append hprefix tailTrace_6304442
  have hstable : (prefixWord ++ tailWord_6304442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304442).length < 2 ^ (prefixWord ++ tailWord_6304442).sum := by decide
  have hdescent : baseEnd_6304442 < baseStart_6304442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304455 : List Nat := [1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4]
def baseStart_6304455 : Nat := 118140960795 + 6304455 * 2 ^ 59
def prefixEnd_6304455 : Nat := 4983230072969 + 3 ^ 40 * 6304455 * 2
def baseEnd_6304455 : Nat := 3237215679641236524518845

theorem tailTrace_6304455 : CollatzResearch.WordTrace tailWord_6304455 prefixEnd_6304455 3237215679641236524518845 := by
  unfold tailWord_6304455
  simp only [CollatzResearch.WordTrace]
  refine ⟨229942364375043725037434819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153294909583362483358289879 229942364375043725037434819)
  ·
    refine ⟨344913546562565587556152229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229942364375043725037434819 344913546562565587556152229)
    ·
      refine ⟨64671289980481047666778543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 344913546562565587556152229 64671289980481047666778543)
      ·
        refine ⟨97006934970721571500167815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 64671289980481047666778543 97006934970721571500167815)
        ·
          refine ⟨145510402456082357250251723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97006934970721571500167815 145510402456082357250251723)
          ·
            refine ⟨218265603684123535875377585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 145510402456082357250251723 218265603684123535875377585)
            ·
              refine ⟨163699202763092651906533189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 218265603684123535875377585 163699202763092651906533189)
              ·
                refine ⟨30693600518079872232474973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 163699202763092651906533189 30693600518079872232474973)
                ·
                  refine ⟨11510100194279952087178115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 30693600518079872232474973 11510100194279952087178115)
                  ·
                    refine ⟨17265150291419928130767173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11510100194279952087178115 17265150291419928130767173)
                    ·
                      refine ⟨3237215679641236524518845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17265150291419928130767173 3237215679641236524518845)
                      ·
                        rfl

theorem cell23_6304455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 4, 3, 1, 4].length) (baseStart_6304455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304455 prefixEnd_6304455 := by exact prefixLift 6304455
  have htrace : WordTrace (prefixWord ++ tailWord_6304455) baseStart_6304455 baseEnd_6304455 := by
    simpa [prefixWord, tailWord_6304455, baseEnd_6304455] using wordTrace_append hprefix tailTrace_6304455
  have hstable : (prefixWord ++ tailWord_6304455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304455).length < 2 ^ (prefixWord ++ tailWord_6304455).sum := by decide
  have hdescent : baseEnd_6304455 < baseStart_6304455 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304472 : List Nat := [2, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4]
def baseStart_6304472 : Nat := 118140960795 + 6304472 * 2 ^ 59
def prefixEnd_6304472 : Nat := 4983230072969 + 3 ^ 40 * 6304472 * 2
def baseEnd_6304472 : Nat := 3237224408812362958006267

theorem tailTrace_6304472 : CollatzResearch.WordTrace tailWord_6304472 prefixEnd_6304472 3237224408812362958006267 := by
  unfold tailWord_6304472
  simp only [CollatzResearch.WordTrace]
  refine ⟨114971492207991068470401835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153295322943988091293869113 114971492207991068470401835)
  ·
    refine ⟨172457238311986602705602753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114971492207991068470401835 172457238311986602705602753)
    ·
      refine ⟨129342928733989952029202065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 172457238311986602705602753 129342928733989952029202065)
      ·
        refine ⟨97007196550492464021901549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129342928733989952029202065 97007196550492464021901549)
        ·
          refine ⟨36377698706434674008213081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 97007196550492464021901549 36377698706434674008213081)
          ·
            refine ⟨27283274029826005506159811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36377698706434674008213081 27283274029826005506159811)
            ·
              refine ⟨40924911044739008259239717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27283274029826005506159811 40924911044739008259239717)
              ·
                refine ⟨7673420820888564048607447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40924911044739008259239717 7673420820888564048607447)
                ·
                  refine ⟨11510131231332846072911171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673420820888564048607447 11510131231332846072911171)
                  ·
                    refine ⟨17265196846999269109366757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11510131231332846072911171 17265196846999269109366757)
                    ·
                      refine ⟨3237224408812362958006267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17265196846999269109366757 3237224408812362958006267)
                      ·
                        rfl

theorem cell23_6304472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 1, 4, 1, 1, 4].length) (baseStart_6304472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304472 prefixEnd_6304472 := by exact prefixLift 6304472
  have htrace : WordTrace (prefixWord ++ tailWord_6304472) baseStart_6304472 baseEnd_6304472 := by
    simpa [prefixWord, tailWord_6304472, baseEnd_6304472] using wordTrace_append hprefix tailTrace_6304472
  have hstable : (prefixWord ++ tailWord_6304472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304472).length < 2 ^ (prefixWord ++ tailWord_6304472).sum := by decide
  have hdescent : baseEnd_6304472 < baseStart_6304472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304483 : List Nat := [1, 1, 1, 7, 1, 3, 1, 3, 1, 1, 3]
def baseStart_6304483 : Nat := 118140960795 + 6304483 * 2 ^ 59
def prefixEnd_6304483 : Nat := 4983230072969 + 3 ^ 40 * 6304483 * 2
def baseEnd_6304483 : Nat := 3237230057099562414968717

theorem tailTrace_6304483 : CollatzResearch.WordTrace tailWord_6304483 prefixEnd_6304483 3237230057099562414968717 := by
  unfold tailWord_6304483
  simp only [CollatzResearch.WordTrace]
  refine ⟨229943385618942285819454103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153295590412628190546302735 229943385618942285819454103)
  ·
    refine ⟨344915078428413428729181155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229943385618942285819454103 344915078428413428729181155)
    ·
      refine ⟨517372617642620143093771733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344915078428413428729181155 517372617642620143093771733)
      ·
        refine ⟨12125920725998909603760275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 517372617642620143093771733 12125920725998909603760275)
        ·
          refine ⟨18188881088998364405640413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12125920725998909603760275 18188881088998364405640413)
          ·
            refine ⟨6820830408374386652115155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18188881088998364405640413 6820830408374386652115155)
            ·
              refine ⟨10231245612561579978172733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820830408374386652115155 10231245612561579978172733)
              ·
                refine ⟨3836717104710592491814775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10231245612561579978172733 3836717104710592491814775)
                ·
                  refine ⟨5755075657065888737722163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836717104710592491814775 5755075657065888737722163)
                  ·
                    refine ⟨8632613485598833106583245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755075657065888737722163 8632613485598833106583245)
                    ·
                      refine ⟨3237230057099562414968717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632613485598833106583245 3237230057099562414968717)
                      ·
                        rfl

theorem cell23_6304483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 3, 1, 3, 1, 1, 3].length) (baseStart_6304483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304483 prefixEnd_6304483 := by exact prefixLift 6304483
  have htrace : WordTrace (prefixWord ++ tailWord_6304483) baseStart_6304483 baseEnd_6304483 := by
    simpa [prefixWord, tailWord_6304483, baseEnd_6304483] using wordTrace_append hprefix tailTrace_6304483
  have hstable : (prefixWord ++ tailWord_6304483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304483).length < 2 ^ (prefixWord ++ tailWord_6304483).sum := by decide
  have hdescent : baseEnd_6304483 < baseStart_6304483 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304495 : List Nat := [1, 1, 2, 1, 5, 4, 9]
def baseStart_6304495 : Nat := 118140960795 + 6304495 * 2 ^ 59
def prefixEnd_6304495 : Nat := 4983230072969 + 3 ^ 40 * 6304495 * 2
def baseEnd_6304495 : Nat := 39965879245276745284181

theorem tailTrace_6304495 : CollatzResearch.WordTrace tailWord_6304495 prefixEnd_6304495 39965879245276745284181 := by
  unfold tailWord_6304495
  simp only [CollatzResearch.WordTrace]
  refine ⟨229943823294898811868890939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153295882196599207912593959 229943823294898811868890939)
  ·
    refine ⟨344915734942348217803336409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229943823294898811868890939 344915734942348217803336409)
    ·
      refine ⟨258686801206761163352502307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 344915734942348217803336409 258686801206761163352502307)
      ·
        refine ⟨388030201810141745028753461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258686801206761163352502307 388030201810141745028753461)
        ·
          refine ⟨36377831419700788596445637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 388030201810141745028753461 36377831419700788596445637)
          ·
            refine ⟨6820843391193897861833557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 36377831419700788596445637 6820843391193897861833557)
            ·
              refine ⟨39965879245276745284181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6820843391193897861833557 39965879245276745284181)
              ·
                rfl

theorem cell23_6304495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 4, 9].length) (baseStart_6304495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304495 prefixEnd_6304495 := by exact prefixLift 6304495
  have htrace : WordTrace (prefixWord ++ tailWord_6304495) baseStart_6304495 baseEnd_6304495 := by
    simpa [prefixWord, tailWord_6304495, baseEnd_6304495] using wordTrace_append hprefix tailTrace_6304495
  have hstable : (prefixWord ++ tailWord_6304495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304495).length < 2 ^ (prefixWord ++ tailWord_6304495).sum := by decide
  have hdescent : baseEnd_6304495 < baseStart_6304495 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304500 : List Nat := [2, 6, 1, 1, 2, 2, 1, 1, 3, 1, 3]
def baseStart_6304500 : Nat := 118140960795 + 6304500 * 2 ^ 59
def prefixEnd_6304500 : Nat := 4983230072969 + 3 ^ 40 * 6304500 * 2
def baseEnd_6304500 : Nat := 3237238786270688848456139

theorem tailTrace_6304500 : CollatzResearch.WordTrace tailWord_6304500 prefixEnd_6304500 3237238786270688848456139 := by
  unfold tailWord_6304500
  simp only [CollatzResearch.WordTrace]
  refine ⟨114972002829940348861411477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153296003773253798481881969 114972002829940348861411477)
  ·
    refine ⟨5389312632653453852878663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 114972002829940348861411477 5389312632653453852878663)
    ·
      refine ⟨8083968948980180779317995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389312632653453852878663 8083968948980180779317995)
      ·
        refine ⟨12125953423470271168976993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8083968948980180779317995 12125953423470271168976993)
        ·
          refine ⟨9094465067602703376732745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12125953423470271168976993 9094465067602703376732745)
          ·
            refine ⟨6820848800702027532549559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9094465067602703376732745 6820848800702027532549559)
            ·
              refine ⟨10231273201053041298824339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6820848800702027532549559 10231273201053041298824339)
              ·
                refine ⟨15346909801579561948236509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10231273201053041298824339 15346909801579561948236509)
                ·
                  refine ⟨5755091175592335730588691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 15346909801579561948236509 5755091175592335730588691)
                  ·
                    refine ⟨8632636763388503595883037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5755091175592335730588691 8632636763388503595883037)
                    ·
                      refine ⟨3237238786270688848456139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632636763388503595883037 3237238786270688848456139)
                      ·
                        rfl

theorem cell23_6304500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 2, 1, 1, 3, 1, 3].length) (baseStart_6304500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304500 prefixEnd_6304500 := by exact prefixLift 6304500
  have htrace : WordTrace (prefixWord ++ tailWord_6304500) baseStart_6304500 baseEnd_6304500 := by
    simpa [prefixWord, tailWord_6304500, baseEnd_6304500] using wordTrace_append hprefix tailTrace_6304500
  have hstable : (prefixWord ++ tailWord_6304500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304500).length < 2 ^ (prefixWord ++ tailWord_6304500).sum := by decide
  have hdescent : baseEnd_6304500 < baseStart_6304500 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304506 : List Nat := [3, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2]
def baseStart_6304506 : Nat := 118140960795 + 6304506 * 2 ^ 59
def prefixEnd_6304506 : Nat := 4983230072969 + 3 ^ 40 * 6304506 * 2
def baseEnd_6304506 : Nat := 3237241867154615824981111

theorem tailTrace_6304506 : CollatzResearch.WordTrace tailWord_6304506 prefixEnd_6304506 3237241867154615824981111 := by
  unfold tailWord_6304506
  simp only [CollatzResearch.WordTrace]
  refine ⟨57486056124464740186885343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153296149665239307165027581 57486056124464740186885343)
  ·
    refine ⟨86229084186697110280328015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57486056124464740186885343 86229084186697110280328015)
    ·
      refine ⟨129343626280045665420492023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86229084186697110280328015 129343626280045665420492023)
      ·
        refine ⟨194015439420068498130738035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 129343626280045665420492023 194015439420068498130738035)
        ·
          refine ⟨291023159130102747196107053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194015439420068498130738035 291023159130102747196107053)
          ·
            refine ⟨109133684673788530198540145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 291023159130102747196107053 109133684673788530198540145)
            ·
              refine ⟨81850263505341397648905109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 109133684673788530198540145 81850263505341397648905109)
              ·
                refine ⟨3836731101812878014792427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 81850263505341397648905109 3836731101812878014792427)
                ·
                  refine ⟨5755096652719317022188641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836731101812878014792427 5755096652719317022188641)
                  ·
                    refine ⟨4316322489539487766641481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755096652719317022188641 4316322489539487766641481)
                    ·
                      refine ⟨3237241867154615824981111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316322489539487766641481 3237241867154615824981111)
                      ·
                        rfl

theorem cell23_6304506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 2, 6, 1, 2, 2].length) (baseStart_6304506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304506 prefixEnd_6304506 := by exact prefixLift 6304506
  have htrace : WordTrace (prefixWord ++ tailWord_6304506) baseStart_6304506 baseEnd_6304506 := by
    simpa [prefixWord, tailWord_6304506, baseEnd_6304506] using wordTrace_append hprefix tailTrace_6304506
  have hstable : (prefixWord ++ tailWord_6304506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304506).length < 2 ^ (prefixWord ++ tailWord_6304506).sum := by decide
  have hdescent : baseEnd_6304506 < baseStart_6304506 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304522 : List Nat := [3, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3]
def baseStart_6304522 : Nat := 118140960795 + 6304522 * 2 ^ 59
def prefixEnd_6304522 : Nat := 4983230072969 + 3 ^ 40 * 6304522 * 2
def baseEnd_6304522 : Nat := 3237250082845087762381037

theorem tailTrace_6304522 : CollatzResearch.WordTrace tailWord_6304522 prefixEnd_6304522 3237250082845087762381037 := by
  unfold tailWord_6304522
  simp only [CollatzResearch.WordTrace]
  refine ⟨57486202016450248870030955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153296538710533996986749213 57486202016450248870030955)
  ·
    refine ⟨86229303024675373305046433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57486202016450248870030955 86229303024675373305046433)
    ·
      refine ⟨64671977268506529978784825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 86229303024675373305046433 64671977268506529978784825)
      ·
        refine ⟨48503982951379897484088619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64671977268506529978784825 48503982951379897484088619)
        ·
          refine ⟨72755974427069846226132929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48503982951379897484088619 72755974427069846226132929)
          ·
            refine ⟨54566980820302384669599697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72755974427069846226132929 54566980820302384669599697)
            ·
              refine ⟨40925235615226788502199773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54566980820302384669599697 40925235615226788502199773)
              ·
                refine ⟨15346963355710045688324915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 40925235615226788502199773 15346963355710045688324915)
                ·
                  refine ⟨23020445033565068532487373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15346963355710045688324915 23020445033565068532487373)
                  ·
                    refine ⟨8632666887586900699682765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23020445033565068532487373 8632666887586900699682765)
                    ·
                      refine ⟨3237250082845087762381037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632666887586900699682765 3237250082845087762381037)
                      ·
                        rfl

theorem cell23_6304522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 3, 1, 3, 3].length) (baseStart_6304522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304522 prefixEnd_6304522 := by exact prefixLift 6304522
  have htrace : WordTrace (prefixWord ++ tailWord_6304522) baseStart_6304522 baseEnd_6304522 := by
    simpa [prefixWord, tailWord_6304522, baseEnd_6304522] using wordTrace_append hprefix tailTrace_6304522
  have hstable : (prefixWord ++ tailWord_6304522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304522).length < 2 ^ (prefixWord ++ tailWord_6304522).sum := by decide
  have hdescent : baseEnd_6304522 < baseStart_6304522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304557 : List Nat := [1, 5, 3, 2, 1, 1, 1, 4, 1, 2, 2]
def baseStart_6304557 : Nat := 118140960795 + 6304557 * 2 ^ 59
def prefixEnd_6304557 : Nat := 4983230072969 + 3 ^ 40 * 6304557 * 2
def baseEnd_6304557 : Nat := 3237268054667995125443377

theorem tailTrace_6304557 : CollatzResearch.WordTrace tailWord_6304557 prefixEnd_6304557 3237268054667995125443377 := by
  unfold tailWord_6304557
  simp only [CollatzResearch.WordTrace]
  refine ⟨229946084620674196457647925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153297389747116130971765283 229946084620674196457647925)
  ·
    refine ⟨21557445433188205917904493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 229946084620674196457647925 21557445433188205917904493)
    ·
      refine ⟨8084042037445577219214185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21557445433188205917904493 8084042037445577219214185)
      ·
        refine ⟨6063031528084182914410639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084042037445577219214185 6063031528084182914410639)
        ·
          refine ⟨9094547292126274371615959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6063031528084182914410639 9094547292126274371615959)
          ·
            refine ⟨13641820938189411557423939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9094547292126274371615959 13641820938189411557423939)
            ·
              refine ⟨20462731407284117336135909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13641820938189411557423939 20462731407284117336135909)
              ·
                refine ⟨3836762138865772000525483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20462731407284117336135909 3836762138865772000525483)
                ·
                  refine ⟨5755143208298658000788225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836762138865772000525483 5755143208298658000788225)
                  ·
                    refine ⟨4316357406223993500591169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5755143208298658000788225 4316357406223993500591169)
                    ·
                      refine ⟨3237268054667995125443377, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316357406223993500591169 3237268054667995125443377)
                      ·
                        rfl

theorem cell23_6304557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 1, 4, 1, 2, 2].length) (baseStart_6304557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304557 prefixEnd_6304557 := by exact prefixLift 6304557
  have htrace : WordTrace (prefixWord ++ tailWord_6304557) baseStart_6304557 baseEnd_6304557 := by
    simpa [prefixWord, tailWord_6304557, baseEnd_6304557] using wordTrace_append hprefix tailTrace_6304557
  have hstable : (prefixWord ++ tailWord_6304557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304557).length < 2 ^ (prefixWord ++ tailWord_6304557).sum := by decide
  have hdescent : baseEnd_6304557 < baseStart_6304557 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304579 : List Nat := [1, 1, 1, 3, 1, 4, 4, 1, 1, 4, 2]
def baseStart_6304579 : Nat := 118140960795 + 6304579 * 2 ^ 59
def prefixEnd_6304579 : Nat := 4983230072969 + 3 ^ 40 * 6304579 * 2
def baseEnd_6304579 : Nat := 3237279351242394039368275

theorem tailTrace_6304579 : CollatzResearch.WordTrace tailWord_6304579 prefixEnd_6304579 3237279351242394039368275 := by
  unfold tailWord_6304579
  simp only [CollatzResearch.WordTrace]
  refine ⟨229946887026594494214948791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153297924684396329476632527 229946887026594494214948791)
  ·
    refine ⟨344920330539891741322423187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 229946887026594494214948791 344920330539891741322423187)
    ·
      refine ⟨517380495809837611983634781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 344920330539891741322423187 517380495809837611983634781)
      ·
        refine ⟨194017685928689104493863043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 517380495809837611983634781 194017685928689104493863043)
        ·
          refine ⟨291026528893033656740794565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 194017685928689104493863043 291026528893033656740794565)
          ·
            refine ⟨54567474167443810638898981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 291026528893033656740794565 54567474167443810638898981)
            ·
              refine ⟨10231401406395714494793559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 54567474167443810638898981 10231401406395714494793559)
              ·
                refine ⟨15347102109593571742190339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10231401406395714494793559 15347102109593571742190339)
                ·
                  refine ⟨23020653164390357613285509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15347102109593571742190339 23020653164390357613285509)
                  ·
                    refine ⟨4316372468323192052491033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 23020653164390357613285509 4316372468323192052491033)
                    ·
                      refine ⟨3237279351242394039368275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4316372468323192052491033 3237279351242394039368275)
                      ·
                        rfl

theorem cell23_6304579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4, 2].length) (baseStart_6304579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304579 prefixEnd_6304579 := by exact prefixLift 6304579
  have htrace : WordTrace (prefixWord ++ tailWord_6304579) baseStart_6304579 baseEnd_6304579 := by
    simpa [prefixWord, tailWord_6304579, baseEnd_6304579] using wordTrace_append hprefix tailTrace_6304579
  have hstable : (prefixWord ++ tailWord_6304579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304579).length < 2 ^ (prefixWord ++ tailWord_6304579).sum := by decide
  have hdescent : baseEnd_6304579 < baseStart_6304579 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304585 : List Nat := [1, 2, 1, 1, 2, 5, 1, 1, 9]
def baseStart_6304585 : Nat := 118140960795 + 6304585 * 2 ^ 59
def prefixEnd_6304585 : Nat := 4983230072969 + 3 ^ 40 * 6304585 * 2
def baseEnd_6304585 : Nat := 359698048014035668432583

theorem tailTrace_6304585 : CollatzResearch.WordTrace tailWord_6304585 prefixEnd_6304585 359698048014035668432583 := by
  unfold tailWord_6304585
  simp only [CollatzResearch.WordTrace]
  refine ⟨229947105864572757239667209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153298070576381838159778139 229947105864572757239667209)
  ·
    refine ⟨172460329398429567929750407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229947105864572757239667209 172460329398429567929750407)
    ·
      refine ⟨258690494097644351894625611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 172460329398429567929750407 258690494097644351894625611)
      ·
        refine ⟨388035741146466527841938417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 258690494097644351894625611 388035741146466527841938417)
        ·
          refine ⟨291026805859849895881453813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 388035741146466527841938417 291026805859849895881453813)
          ·
            refine ⟨27283763049360927738886295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 291026805859849895881453813 27283763049360927738886295)
            ·
              refine ⟨40925644574041391608329443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27283763049360927738886295 40925644574041391608329443)
              ·
                refine ⟨61388466861062087412494165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40925644574041391608329443 61388466861062087412494165)
                ·
                  refine ⟨359698048014035668432583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 61388466861062087412494165 359698048014035668432583)
                  ·
                    rfl

theorem cell23_6304585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 5, 1, 1, 9].length) (baseStart_6304585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304585 prefixEnd_6304585 := by exact prefixLift 6304585
  have htrace : WordTrace (prefixWord ++ tailWord_6304585) baseStart_6304585 baseEnd_6304585 := by
    simpa [prefixWord, tailWord_6304585, baseEnd_6304585] using wordTrace_append hprefix tailTrace_6304585
  have hstable : (prefixWord ++ tailWord_6304585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304585).length < 2 ^ (prefixWord ++ tailWord_6304585).sum := by decide
  have hdescent : baseEnd_6304585 < baseStart_6304585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304629 : List Nat := [1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 3]
def baseStart_6304629 : Nat := 118140960795 + 6304629 * 2 ^ 59
def prefixEnd_6304629 : Nat := 4983230072969 + 3 ^ 40 * 6304629 * 2
def baseEnd_6304629 : Nat := 3237305025275118843743045

theorem tailTrace_6304629 : CollatzResearch.WordTrace tailWord_6304629 prefixEnd_6304629 3237305025275118843743045 := by
  unfold tailWord_6304629
  simp only [CollatzResearch.WordTrace]
  refine ⟨229948710676413352754268941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153299140450942235169512627 229948710676413352754268941)
  ·
    refine ⟨86230766503655007282850853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229948710676413352754268941 86230766503655007282850853)
    ·
      refine ⟨16168268719435313865534535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 86230766503655007282850853 16168268719435313865534535)
      ·
        refine ⟨24252403079152970798301803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16168268719435313865534535 24252403079152970798301803)
        ·
          refine ⟨36378604618729456197452705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24252403079152970798301803 36378604618729456197452705)
          ·
            refine ⟨27283953464047092148089529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36378604618729456197452705 27283953464047092148089529)
            ·
              refine ⟨20462965098035319111067147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27283953464047092148089529 20462965098035319111067147)
              ·
                refine ⟨30694447647052978666600721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20462965098035319111067147 30694447647052978666600721)
                ·
                  refine ⟨23020835735289733999950541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 30694447647052978666600721 23020835735289733999950541)
                  ·
                    refine ⟨8632813400733650249981453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 23020835735289733999950541 8632813400733650249981453)
                    ·
                      refine ⟨3237305025275118843743045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632813400733650249981453 3237305025275118843743045)
                      ·
                        rfl

theorem cell23_6304629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_6304629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304629 prefixEnd_6304629 := by exact prefixLift 6304629
  have htrace : WordTrace (prefixWord ++ tailWord_6304629) baseStart_6304629 baseEnd_6304629 := by
    simpa [prefixWord, tailWord_6304629, baseEnd_6304629] using wordTrace_append hprefix tailTrace_6304629
  have hstable : (prefixWord ++ tailWord_6304629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304629).length < 2 ^ (prefixWord ++ tailWord_6304629).sum := by decide
  have hdescent : baseEnd_6304629 < baseStart_6304629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304652 : List Nat := [2, 2, 1, 2, 1, 2, 4, 1, 1, 3, 4]
def baseStart_6304652 : Nat := 118140960795 + 6304652 * 2 ^ 59
def prefixEnd_6304652 : Nat := 4983230072969 + 3 ^ 40 * 6304652 * 2
def baseEnd_6304652 : Nat := 3237316835330172253755439

theorem tailTrace_6304652 : CollatzResearch.WordTrace tailWord_6304652 prefixEnd_6304652 3237316835330172253755439 := by
  unfold tailWord_6304652
  simp only [CollatzResearch.WordTrace]
  refine ⟨114974774777665013841178105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153299699703553351788237473 114974774777665013841178105)
  ·
    refine ⟨86231081083248760380883579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114974774777665013841178105 86231081083248760380883579)
    ·
      refine ⟨129346621624873140571325369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86231081083248760380883579 129346621624873140571325369)
      ·
        refine ⟨97009966218654855428494027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129346621624873140571325369 97009966218654855428494027)
        ·
          refine ⟨145514949327982283142741041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 97009966218654855428494027 145514949327982283142741041)
          ·
            refine ⟨109136211995986712357055781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 145514949327982283142741041 109136211995986712357055781)
            ·
              refine ⟨20463039749247508566947959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 109136211995986712357055781 20463039749247508566947959)
              ·
                refine ⟨30694559623871262850421939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20463039749247508566947959 30694559623871262850421939)
                ·
                  refine ⟨46041839435806894275632909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 30694559623871262850421939 46041839435806894275632909)
                  ·
                    refine ⟨17265689788427585353362341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 46041839435806894275632909 17265689788427585353362341)
                    ·
                      refine ⟨3237316835330172253755439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17265689788427585353362341 3237316835330172253755439)
                      ·
                        rfl

theorem cell23_6304652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 1, 1, 3, 4].length) (baseStart_6304652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304652 prefixEnd_6304652 := by exact prefixLift 6304652
  have htrace : WordTrace (prefixWord ++ tailWord_6304652) baseStart_6304652 baseEnd_6304652 := by
    simpa [prefixWord, tailWord_6304652, baseEnd_6304652] using wordTrace_append hprefix tailTrace_6304652
  have hstable : (prefixWord ++ tailWord_6304652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304652).length < 2 ^ (prefixWord ++ tailWord_6304652).sum := by decide
  have hdescent : baseEnd_6304652 < baseStart_6304652 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304669 : List Nat := [1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 4]
def baseStart_6304669 : Nat := 118140960795 + 6304669 * 2 ^ 59
def prefixEnd_6304669 : Nat := 4983230072969 + 3 ^ 40 * 6304669 * 2
def baseEnd_6304669 : Nat := 3237325564501298687242861

theorem tailTrace_6304669 : CollatzResearch.WordTrace tailWord_6304669 prefixEnd_6304669 3237325564501298687242861 := by
  unfold tailWord_6304669
  simp only [CollatzResearch.WordTrace]
  refine ⟨229950169596268439585725061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153300113064178959723816707 229950169596268439585725061)
  ·
    refine ⟨43115656799300332422323449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 229950169596268439585725061 43115656799300332422323449)
    ·
      refine ⟨32336742599475249316742587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 43115656799300332422323449 32336742599475249316742587)
      ·
        refine ⟨48505113899212873975113881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32336742599475249316742587 48505113899212873975113881)
        ·
          refine ⟨36378835424409655481335411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48505113899212873975113881 36378835424409655481335411)
          ·
            refine ⟨54568253136614483222003117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36378835424409655481335411 54568253136614483222003117)
            ·
              refine ⟨20463094926230431208251169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 54568253136614483222003117 20463094926230431208251169)
              ·
                refine ⟨15347321194672823406188377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20463094926230431208251169 15347321194672823406188377)
                ·
                  refine ⟨11510490896004617554641283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15347321194672823406188377 11510490896004617554641283)
                  ·
                    refine ⟨17265736344006926331961925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11510490896004617554641283 17265736344006926331961925)
                    ·
                      refine ⟨3237325564501298687242861, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17265736344006926331961925 3237325564501298687242861)
                      ·
                        rfl

theorem cell23_6304669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_6304669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304669 prefixEnd_6304669 := by exact prefixLift 6304669
  have htrace : WordTrace (prefixWord ++ tailWord_6304669) baseStart_6304669 baseEnd_6304669 := by
    simpa [prefixWord, tailWord_6304669, baseEnd_6304669] using wordTrace_append hprefix tailTrace_6304669
  have hstable : (prefixWord ++ tailWord_6304669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304669).length < 2 ^ (prefixWord ++ tailWord_6304669).sum := by decide
  have hdescent : baseEnd_6304669 < baseStart_6304669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304726 : List Nat := [5, 2, 1, 1, 2, 1, 1, 4, 6]
def baseStart_6304726 : Nat := 118140960795 + 6304726 * 2 ^ 59
def prefixEnd_6304726 : Nat := 4983230072969 + 3 ^ 40 * 6304726 * 2
def baseEnd_6304726 : Nat := 359706092544289440470011

theorem tailTrace_6304726 : CollatzResearch.WordTrace tailWord_6304726 prefixEnd_6304726 359706092544289440470011 := by
  unfold tailWord_6304726
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372015534816371145034377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 153301499038041292213700021 14372015534816371145034377)
  ·
    refine ⟨10779011651112278358775783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14372015534816371145034377 10779011651112278358775783)
    ·
      refine ⟨16168517476668417538163675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10779011651112278358775783 16168517476668417538163675)
      ·
        refine ⟨24252776215002626307245513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16168517476668417538163675 24252776215002626307245513)
        ·
          refine ⟨18189582161251969730434135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24252776215002626307245513 18189582161251969730434135)
          ·
            refine ⟨27284373241877954595651203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18189582161251969730434135 27284373241877954595651203)
            ·
              refine ⟨40926559862816931893476805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27284373241877954595651203 40926559862816931893476805)
              ·
                refine ⟨7673729974278174730026901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 40926559862816931893476805 7673729974278174730026901)
                ·
                  refine ⟨359706092544289440470011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7673729974278174730026901 359706092544289440470011)
                  ·
                    rfl

theorem cell23_6304726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_6304726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304726 prefixEnd_6304726 := by exact prefixLift 6304726
  have htrace : WordTrace (prefixWord ++ tailWord_6304726) baseStart_6304726 baseEnd_6304726 := by
    simpa [prefixWord, tailWord_6304726, baseEnd_6304726] using wordTrace_append hprefix tailTrace_6304726
  have hstable : (prefixWord ++ tailWord_6304726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304726).length < 2 ^ (prefixWord ++ tailWord_6304726).sum := by decide
  have hdescent : baseEnd_6304726 < baseStart_6304726 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304730 : List Nat := [3, 1, 1, 2, 4, 3, 2, 2, 1, 4]
def baseStart_6304730 : Nat := 118140960795 + 6304730 * 2 ^ 59
def prefixEnd_6304730 : Nat := 4983230072969 + 3 ^ 40 * 6304730 * 2
def baseEnd_6304730 : Nat := 1079118962273740982860027

theorem tailTrace_6304730 : CollatzResearch.WordTrace tailWord_6304730 prefixEnd_6304730 1079118962273740982860027 := by
  unfold tailWord_6304730
  simp only [CollatzResearch.WordTrace]
  refine ⟨57488098612261861750923911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 153301596299364964669130429 57488098612261861750923911)
  ·
    refine ⟨86232147918392792626385867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 57488098612261861750923911 86232147918392792626385867)
    ·
      refine ⟨129348221877589188939578801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 86232147918392792626385867 129348221877589188939578801)
      ·
        refine ⟨97011166408191891704684101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 129348221877589188939578801 97011166408191891704684101)
        ·
          refine ⟨18189593701535979694628269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 97011166408191891704684101 18189593701535979694628269)
          ·
            refine ⟨6821097638075992385485601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18189593701535979694628269 6821097638075992385485601)
            ·
              refine ⟨5115823228556994289114201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6821097638075992385485601 5115823228556994289114201)
              ·
                refine ⟨3836867421417745716835651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5115823228556994289114201 3836867421417745716835651)
                ·
                  refine ⟨5755301132126618575253477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3836867421417745716835651 5755301132126618575253477)
                  ·
                    refine ⟨1079118962273740982860027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5755301132126618575253477 1079118962273740982860027)
                    ·
                      rfl

theorem cell23_6304730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 2, 2, 1, 4].length) (baseStart_6304730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304730 prefixEnd_6304730 := by exact prefixLift 6304730
  have htrace : WordTrace (prefixWord ++ tailWord_6304730) baseStart_6304730 baseEnd_6304730 := by
    simpa [prefixWord, tailWord_6304730, baseEnd_6304730] using wordTrace_append hprefix tailTrace_6304730
  have hstable : (prefixWord ++ tailWord_6304730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304730).length < 2 ^ (prefixWord ++ tailWord_6304730).sum := by decide
  have hdescent : baseEnd_6304730 < baseStart_6304730 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304757 : List Nat := [1, 3, 5, 2, 2, 1, 1, 1, 2, 2, 3]
def baseStart_6304757 : Nat := 118140960795 + 6304757 * 2 ^ 59
def prefixEnd_6304757 : Nat := 4983230072969 + 3 ^ 40 * 6304757 * 2
def baseEnd_6304757 : Nat := 3237370750798894342942457

theorem tailTrace_6304757 : CollatzResearch.WordTrace tailWord_6304757 prefixEnd_6304757 3237370750798894342942457 := by
  unfold tailWord_6304757
  simp only [CollatzResearch.WordTrace]
  refine ⟨229953379219949630614928525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153302252813299753743285683 229953379219949630614928525)
  ·
    refine ⟨86232517207481111480598197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 229953379219949630614928525 86232517207481111480598197)
    ·
      refine ⟨8084298488201354201306081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 86232517207481111480598197 8084298488201354201306081)
      ·
        refine ⟨6063223866151015650979561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084298488201354201306081 6063223866151015650979561)
        ·
          refine ⟨4547417899613261738234671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6063223866151015650979561 4547417899613261738234671)
          ·
            refine ⟨6821126849419892607352007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4547417899613261738234671 6821126849419892607352007)
            ·
              refine ⟨10231690274129838911028011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6821126849419892607352007 10231690274129838911028011)
              ·
                refine ⟨15347535411194758366542017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10231690274129838911028011 15347535411194758366542017)
                ·
                  refine ⟨11510651558396068774906513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 15347535411194758366542017 11510651558396068774906513)
                  ·
                    refine ⟨8632988668797051581179885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 11510651558396068774906513 8632988668797051581179885)
                    ·
                      refine ⟨3237370750798894342942457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8632988668797051581179885 3237370750798894342942457)
                      ·
                        rfl

theorem cell23_6304757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_6304757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304757 prefixEnd_6304757 := by exact prefixLift 6304757
  have htrace : WordTrace (prefixWord ++ tailWord_6304757) baseStart_6304757 baseEnd_6304757 := by
    simpa [prefixWord, tailWord_6304757, baseEnd_6304757] using wordTrace_append hprefix tailTrace_6304757
  have hstable : (prefixWord ++ tailWord_6304757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304757).length < 2 ^ (prefixWord ++ tailWord_6304757).sum := by decide
  have hdescent : baseEnd_6304757 < baseStart_6304757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304769 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 1, 6]
def baseStart_6304769 : Nat := 118140960795 + 6304769 * 2 ^ 59
def prefixEnd_6304769 : Nat := 4983230072969 + 3 ^ 40 * 6304769 * 2
def baseEnd_6304769 : Nat := 1079125637522249431997467

theorem tailTrace_6304769 : CollatzResearch.WordTrace tailWord_6304769 prefixEnd_6304769 1079125637522249431997467 := by
  unfold tailWord_6304769
  simp only [CollatzResearch.WordTrace]
  refine ⟨229953816895906156664365361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 153302544597270771109576907 229953816895906156664365361)
  ·
    refine ⟨172465362671929617498274021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 229953816895906156664365361 172465362671929617498274021)
    ·
      refine ⟨32337255500986803280926379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 172465362671929617498274021 32337255500986803280926379)
      ·
        refine ⟨48505883251480204921389569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32337255500986803280926379 48505883251480204921389569)
        ·
          refine ⟨36379412438610153691042177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48505883251480204921389569 36379412438610153691042177)
          ·
            refine ⟨27284559328957615268281633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36379412438610153691042177 27284559328957615268281633)
            ·
              refine ⟨20463419496718211451211225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27284559328957615268281633 20463419496718211451211225)
              ·
                refine ⟨15347564622538658588408419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20463419496718211451211225 15347564622538658588408419)
                ·
                  refine ⟨23021346933807987882612629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15347564622538658588408419 23021346933807987882612629)
                  ·
                    refine ⟨1079125637522249431997467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 23021346933807987882612629 1079125637522249431997467)
                    ·
                      rfl

theorem cell23_6304769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 1, 6].length) (baseStart_6304769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304769 prefixEnd_6304769 := by exact prefixLift 6304769
  have htrace : WordTrace (prefixWord ++ tailWord_6304769) baseStart_6304769 baseEnd_6304769 := by
    simpa [prefixWord, tailWord_6304769, baseEnd_6304769] using wordTrace_append hprefix tailTrace_6304769
  have hstable : (prefixWord ++ tailWord_6304769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304769).length < 2 ^ (prefixWord ++ tailWord_6304769).sum := by decide
  have hdescent : baseEnd_6304769 < baseStart_6304769 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304776 : List Nat := [2, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4]
def baseStart_6304776 : Nat := 118140960795 + 6304776 * 2 ^ 59
def prefixEnd_6304776 : Nat := 4983230072969 + 3 ^ 40 * 6304776 * 2
def baseEnd_6304776 : Nat := 3237380506931329768604869

theorem tailTrace_6304776 : CollatzResearch.WordTrace tailWord_6304776 prefixEnd_6304776 3237380506931329768604869 := by
  unfold tailWord_6304776
  simp only [CollatzResearch.WordTrace]
  refine ⟨114977036103440398429935091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153302714804587197906580121 114977036103440398429935091)
  ·
    refine ⟨172465554155160597644902637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 114977036103440398429935091 172465554155160597644902637)
    ·
      refine ⟨64674582808185224116838489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 172465554155160597644902637 64674582808185224116838489)
      ·
        refine ⟨48505937106138918087628867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 64674582808185224116838489 48505937106138918087628867)
        ·
          refine ⟨72758905659208377131443301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48505937106138918087628867 72758905659208377131443301)
          ·
            refine ⟨13642294811101570712145619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 72758905659208377131443301 13642294811101570712145619)
            ·
              refine ⟨20463442216652356068218429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13642294811101570712145619 20463442216652356068218429)
              ·
                refine ⟨7673790831244633525581911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20463442216652356068218429 7673790831244633525581911)
                ·
                  refine ⟨11510686246866950288372867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7673790831244633525581911 11510686246866950288372867)
                  ·
                    refine ⟨17266029370300425432559301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 11510686246866950288372867 17266029370300425432559301)
                    ·
                      refine ⟨3237380506931329768604869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 17266029370300425432559301 3237380506931329768604869)
                      ·
                        rfl

theorem cell23_6304776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_6304776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304776 prefixEnd_6304776 := by exact prefixLift 6304776
  have htrace : WordTrace (prefixWord ++ tailWord_6304776) baseStart_6304776 baseEnd_6304776 := by
    simpa [prefixWord, tailWord_6304776, baseEnd_6304776] using wordTrace_append hprefix tailTrace_6304776
  have hstable : (prefixWord ++ tailWord_6304776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304776).length < 2 ^ (prefixWord ++ tailWord_6304776).sum := by decide
  have hdescent : baseEnd_6304776 < baseStart_6304776 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6304796 : List Nat := [2, 2, 3, 1, 4, 1, 1, 2, 1, 1, 5]
def baseStart_6304796 : Nat := 118140960795 + 6304796 * 2 ^ 59
def prefixEnd_6304796 : Nat := 4983230072969 + 3 ^ 40 * 6304796 * 2
def baseEnd_6304796 : Nat := 3237390776544419690354777

theorem tailTrace_6304796 : CollatzResearch.WordTrace tailWord_6304796 prefixEnd_6304796 3237390776544419690354777 := by
  unfold tailWord_6304796
  simp only [CollatzResearch.WordTrace]
  refine ⟨114977400833404170137799121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 153303201111205560183732161 114977400833404170137799121)
  ·
    refine ⟨86233050625053127603349341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 114977400833404170137799121 86233050625053127603349341)
    ·
      refine ⟨32337393984394922851256003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 86233050625053127603349341 32337393984394922851256003)
      ·
        refine ⟨48506090976592384276884005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32337393984394922851256003 48506090976592384276884005)
        ·
          refine ⟨9094892058111072051915751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 48506090976592384276884005 9094892058111072051915751)
          ·
            refine ⟨13642338087166608077873627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9094892058111072051915751 13642338087166608077873627)
            ·
              refine ⟨20463507130749912116810441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13642338087166608077873627 20463507130749912116810441)
              ·
                refine ⟨15347630348062434087607831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20463507130749912116810441 15347630348062434087607831)
                ·
                  refine ⟨23021445522093651131411747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 15347630348062434087607831 23021445522093651131411747)
                  ·
                    refine ⟨34532168283140476697117621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 23021445522093651131411747 34532168283140476697117621)
                    ·
                      refine ⟨3237390776544419690354777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 34532168283140476697117621 3237390776544419690354777)
                      ·
                        rfl

theorem cell23_6304796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 1, 1, 5].length) (baseStart_6304796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6304796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6304796 prefixEnd_6304796 := by exact prefixLift 6304796
  have htrace : WordTrace (prefixWord ++ tailWord_6304796) baseStart_6304796 baseEnd_6304796 := by
    simpa [prefixWord, tailWord_6304796, baseEnd_6304796] using wordTrace_append hprefix tailTrace_6304796
  have hstable : (prefixWord ++ tailWord_6304796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6304796).length < 2 ^ (prefixWord ++ tailWord_6304796).sum := by decide
  have hdescent : baseEnd_6304796 < baseStart_6304796 := by decide
  rcases family_descends (prefixWord ++ tailWord_6304796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
