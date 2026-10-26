import V185TrunkScan20Chunk063

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_390280 : List Nat := [2, 1, 3, 4, 3, 7]
def baseStart_390280 : Nat := 118140960795 + 390280 * 2 ^ 59
def prefixEnd_390280 : Nat := 4983230072969 + 3 ^ 40 * 390280 * 2
def baseEnd_390280 : Nat := 6597571352653111486589

theorem tailTrace_390280 : CollatzResearch.WordTrace tailWord_390280 prefixEnd_390280 6597571352653111486589 := by
  unfold tailWord_390280
  simp only [CollatzResearch.WordTrace]
  refine ⟨7117340513044844681236147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9489787350726459574981529 7117340513044844681236147)
  ·
    refine ⟨10676010769567267021854221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7117340513044844681236147 10676010769567267021854221)
    ·
      refine ⟨4003504038587725133195333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10676010769567267021854221 4003504038587725133195333)
      ·
        refine ⟨750657007235198462474125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4003504038587725133195333 750657007235198462474125)
        ·
          refine ⟨281496377713199423427797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 750657007235198462474125 281496377713199423427797)
          ·
            refine ⟨6597571352653111486589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 281496377713199423427797 6597571352653111486589)
            ·
              rfl

theorem cell20_390280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 7].length) (baseStart_390280 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390280 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390280 prefixEnd_390280 := by exact prefixLift 390280
  have htrace : WordTrace (prefixWord ++ tailWord_390280) baseStart_390280 baseEnd_390280 := by
    simpa [prefixWord, tailWord_390280, baseEnd_390280] using wordTrace_append hprefix tailTrace_390280
  have hstable : (prefixWord ++ tailWord_390280).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390280).length < 2 ^ (prefixWord ++ tailWord_390280).sum := by decide
  have hdescent : baseEnd_390280 < baseStart_390280 := by decide
  rcases family_descends (prefixWord ++ tailWord_390280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390290 : List Nat := [3, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_390290 : Nat := 118140960795 + 390290 * 2 ^ 59
def prefixEnd_390290 : Nat := 4983230072969 + 3 ^ 40 * 390290 * 2
def baseEnd_390290 : Nat := 178138990794118419804529

theorem tailTrace_390290 : CollatzResearch.WordTrace tailWord_390290 prefixEnd_390290 178138990794118419804529 := by
  unfold tailWord_390290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3558761439013365267584081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9490030504035640713557549 3558761439013365267584081)
  ·
    refine ⟨2669071079260023950688061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3558761439013365267584081 2669071079260023950688061)
    ·
      refine ⟨1000901654722508981508023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2669071079260023950688061 1000901654722508981508023)
      ·
        refine ⟨1501352482083763472262035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1000901654722508981508023 1501352482083763472262035)
        ·
          refine ⟨2252028723125645208393053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1501352482083763472262035 2252028723125645208393053)
          ·
            refine ⟨844510771172116953147395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2252028723125645208393053 844510771172116953147395)
            ·
              refine ⟨1266766156758175429721093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844510771172116953147395 1266766156758175429721093)
              ·
                refine ⟨237518654392157893072705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1266766156758175429721093 237518654392157893072705)
                ·
                  refine ⟨178138990794118419804529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237518654392157893072705 178138990794118419804529)
                  ·
                    rfl

theorem cell20_390290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_390290 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390290 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390290 prefixEnd_390290 := by exact prefixLift 390290
  have htrace : WordTrace (prefixWord ++ tailWord_390290) baseStart_390290 baseEnd_390290 := by
    simpa [prefixWord, tailWord_390290, baseEnd_390290] using wordTrace_append hprefix tailTrace_390290
  have hstable : (prefixWord ++ tailWord_390290).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390290).length < 2 ^ (prefixWord ++ tailWord_390290).sum := by decide
  have hdescent : baseEnd_390290 < baseStart_390290 := by decide
  rcases family_descends (prefixWord ++ tailWord_390290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390311 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 4]
def baseStart_390311 : Nat := 118140960795 + 390311 * 2 ^ 59
def prefixEnd_390311 : Nat := 4983230072969 + 3 ^ 40 * 390311 * 2
def baseEnd_390311 : Nat := 178148575766335680104443

theorem tailTrace_390311 : CollatzResearch.WordTrace tailWord_390311 prefixEnd_390311 178148575766335680104443 := by
  unfold tailWord_390311
  simp only [CollatzResearch.WordTrace]
  refine ⟨14235811688977381656850787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9490541125984921104567191 14235811688977381656850787)
  ·
    refine ⟨21353717533466072485276181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14235811688977381656850787 21353717533466072485276181)
    ·
      refine ⟨1000955509381222147747321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21353717533466072485276181 1000955509381222147747321)
      ·
        refine ⟨750716632035916610810491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1000955509381222147747321 750716632035916610810491)
        ·
          refine ⟨1126074948053874916215737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 750716632035916610810491 1126074948053874916215737)
          ·
            refine ⟨844556211040406187161803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126074948053874916215737 844556211040406187161803)
            ·
              refine ⟨1266834316560609280742705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844556211040406187161803 1266834316560609280742705)
              ·
                refine ⟨950125737420456960557029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1266834316560609280742705 950125737420456960557029)
                ·
                  refine ⟨178148575766335680104443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950125737420456960557029 178148575766335680104443)
                  ·
                    rfl

theorem cell20_390311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 4].length) (baseStart_390311 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390311 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390311 prefixEnd_390311 := by exact prefixLift 390311
  have htrace : WordTrace (prefixWord ++ tailWord_390311) baseStart_390311 baseEnd_390311 := by
    simpa [prefixWord, tailWord_390311, baseEnd_390311] using wordTrace_append hprefix tailTrace_390311
  have hstable : (prefixWord ++ tailWord_390311).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390311).length < 2 ^ (prefixWord ++ tailWord_390311).sum := by decide
  have hdescent : baseEnd_390311 < baseStart_390311 := by decide
  rcases family_descends (prefixWord ++ tailWord_390311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390373 : List Nat := [1, 3, 1, 4, 3, 2, 2, 4]
def baseStart_390373 : Nat := 118140960795 + 390373 * 2 ^ 59
def prefixEnd_390373 : Nat := 4983230072969 + 3 ^ 40 * 390373 * 2
def baseEnd_390373 : Nat := 59392291418579673345841

theorem tailTrace_390373 : CollatzResearch.WordTrace tailWord_390373 prefixEnd_390373 59392291418579673345841 := by
  unfold tailWord_390373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14238073014752766245607773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9492048676501844163738515 14238073014752766245607773)
  ·
    refine ⟨5339277380532287342102915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14238073014752766245607773 5339277380532287342102915)
    ·
      refine ⟨8008916070798431013154373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5339277380532287342102915 8008916070798431013154373)
      ·
        refine ⟨1501671763274705814966445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8008916070798431013154373 1501671763274705814966445)
        ·
          refine ⟨563126911228014680612417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1501671763274705814966445 563126911228014680612417)
          ·
            refine ⟨422345183421011010459313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563126911228014680612417 422345183421011010459313)
            ·
              refine ⟨316758887565758257844485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422345183421011010459313 316758887565758257844485)
              ·
                refine ⟨59392291418579673345841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316758887565758257844485 59392291418579673345841)
                ·
                  rfl

theorem cell20_390373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 2, 2, 4].length) (baseStart_390373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390373 prefixEnd_390373 := by exact prefixLift 390373
  have htrace : WordTrace (prefixWord ++ tailWord_390373) baseStart_390373 baseEnd_390373 := by
    simpa [prefixWord, tailWord_390373, baseEnd_390373] using wordTrace_append hprefix tailTrace_390373
  have hstable : (prefixWord ++ tailWord_390373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390373).length < 2 ^ (prefixWord ++ tailWord_390373).sum := by decide
  have hdescent : baseEnd_390373 < baseStart_390373 := by decide
  rcases family_descends (prefixWord ++ tailWord_390373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390383 : List Nat := [1, 1, 2, 1, 8, 1, 1, 3, 2]
def baseStart_390383 : Nat := 118140960795 + 390383 * 2 ^ 59
def prefixEnd_390383 : Nat := 4983230072969 + 3 ^ 40 * 390383 * 2
def baseEnd_390383 : Nat := 178181438528223429704149

theorem tailTrace_390383 : CollatzResearch.WordTrace tailWord_390383 prefixEnd_390383 178181438528223429704149 := by
  unfold tailWord_390383
  simp only [CollatzResearch.WordTrace]
  refine ⟨14238437744716537953471803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9492291829811025302314535 14238437744716537953471803)
  ·
    refine ⟨21357656617074806930207705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14238437744716537953471803 21357656617074806930207705)
    ·
      refine ⟨16018242462806105197655779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21357656617074806930207705 16018242462806105197655779)
      ·
        refine ⟨24027363694209157796483669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16018242462806105197655779 24027363694209157796483669)
        ·
          refine ⟨281570668291513567927543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 24027363694209157796483669 281570668291513567927543)
          ·
            refine ⟨422356002437270351891315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281570668291513567927543 422356002437270351891315)
            ·
              refine ⟨633534003655905527836973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422356002437270351891315 633534003655905527836973)
              ·
                refine ⟨237575251370964572938865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633534003655905527836973 237575251370964572938865)
                ·
                  refine ⟨178181438528223429704149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237575251370964572938865 178181438528223429704149)
                  ·
                    rfl

theorem cell20_390383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 3, 2].length) (baseStart_390383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390383 prefixEnd_390383 := by exact prefixLift 390383
  have htrace : WordTrace (prefixWord ++ tailWord_390383) baseStart_390383 baseEnd_390383 := by
    simpa [prefixWord, tailWord_390383, baseEnd_390383] using wordTrace_append hprefix tailTrace_390383
  have hstable : (prefixWord ++ tailWord_390383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390383).length < 2 ^ (prefixWord ++ tailWord_390383).sum := by decide
  have hdescent : baseEnd_390383 < baseStart_390383 := by decide
  rcases family_descends (prefixWord ++ tailWord_390383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390387 : List Nat := [1, 1, 1, 2, 2, 5, 3, 3, 2]
def baseStart_390387 : Nat := 118140960795 + 390387 * 2 ^ 59
def prefixEnd_390387 : Nat := 4983230072969 + 3 ^ 40 * 390387 * 2
def baseEnd_390387 : Nat := 178183264237217193570799

theorem tailTrace_390387 : CollatzResearch.WordTrace tailWord_390387 prefixEnd_390387 178183264237217193570799 := by
  unfold tailWord_390387
  simp only [CollatzResearch.WordTrace]
  refine ⟨14238583636702046636617415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9492389091134697757744943 14238583636702046636617415)
  ·
    refine ⟨21357875455053069954926123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14238583636702046636617415 21357875455053069954926123)
    ·
      refine ⟨32036813182579604932389185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21357875455053069954926123 32036813182579604932389185)
      ·
        refine ⟨24027609886934703699291889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32036813182579604932389185 24027609886934703699291889)
        ·
          refine ⟨18020707415201027774468917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24027609886934703699291889 18020707415201027774468917)
          ·
            refine ⟨1689441320175096353856461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 18020707415201027774468917 1689441320175096353856461)
            ·
              refine ⟨633540495065661132696173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1689441320175096353856461 633540495065661132696173)
              ·
                refine ⟨237577685649622924761065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633540495065661132696173 237577685649622924761065)
                ·
                  refine ⟨178183264237217193570799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237577685649622924761065 178183264237217193570799)
                  ·
                    rfl

theorem cell20_390387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 3, 3, 2].length) (baseStart_390387 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390387 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390387 prefixEnd_390387 := by exact prefixLift 390387
  have htrace : WordTrace (prefixWord ++ tailWord_390387) baseStart_390387 baseEnd_390387 := by
    simpa [prefixWord, tailWord_390387, baseEnd_390387] using wordTrace_append hprefix tailTrace_390387
  have hstable : (prefixWord ++ tailWord_390387).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390387).length < 2 ^ (prefixWord ++ tailWord_390387).sum := by decide
  have hdescent : baseEnd_390387 < baseStart_390387 := by decide
  rcases family_descends (prefixWord ++ tailWord_390387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390463 : List Nat := [1, 1, 2, 2, 4, 3, 1, 4, 2]
def baseStart_390463 : Nat := 118140960795 + 390463 * 2 ^ 59
def prefixEnd_390463 : Nat := 4983230072969 + 3 ^ 40 * 390463 * 2
def baseEnd_390463 : Nat := 178217952708098707037155

theorem tailTrace_390463 : CollatzResearch.WordTrace tailWord_390463 prefixEnd_390463 178217952708098707037155 := by
  unfold tailWord_390463
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241355584426711616384043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9494237056284474410922695 14241355584426711616384043)
  ·
    refine ⟨21362033376640067424576065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14241355584426711616384043 21362033376640067424576065)
    ·
      refine ⟨16021525032480050568432049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21362033376640067424576065 16021525032480050568432049)
      ·
        refine ⟨12016143774360037926324037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16021525032480050568432049 12016143774360037926324037)
        ·
          refine ⟨2253026957692507111185757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12016143774360037926324037 2253026957692507111185757)
          ·
            refine ⟨844885109134690166694659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2253026957692507111185757 844885109134690166694659)
            ·
              refine ⟨1267327663702035250041989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 844885109134690166694659 1267327663702035250041989)
              ·
                refine ⟨237623936944131609382873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1267327663702035250041989 237623936944131609382873)
                ·
                  refine ⟨178217952708098707037155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237623936944131609382873 178217952708098707037155)
                  ·
                    rfl

theorem cell20_390463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 4, 2].length) (baseStart_390463 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390463 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390463 prefixEnd_390463 := by exact prefixLift 390463
  have htrace : WordTrace (prefixWord ++ tailWord_390463) baseStart_390463 baseEnd_390463 := by
    simpa [prefixWord, tailWord_390463, baseEnd_390463] using wordTrace_append hprefix tailTrace_390463
  have hstable : (prefixWord ++ tailWord_390463).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390463).length < 2 ^ (prefixWord ++ tailWord_390463).sum := by decide
  have hdescent : baseEnd_390463 < baseStart_390463 := by decide
  rcases family_descends (prefixWord ++ tailWord_390463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390467 : List Nat := [1, 1, 1, 3, 1, 3, 1, 5, 4]
def baseStart_390467 : Nat := 118140960795 + 390467 * 2 ^ 59
def prefixEnd_390467 : Nat := 4983230072969 + 3 ^ 40 * 390467 * 2
def baseEnd_390467 : Nat := 178219778417092470903805

theorem tailTrace_390467 : CollatzResearch.WordTrace tailWord_390467 prefixEnd_390467 178219778417092470903805 := by
  unfold tailWord_390467
  simp only [CollatzResearch.WordTrace]
  refine ⟨14241501476412220299529655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9494334317608146866353103 14241501476412220299529655)
  ·
    refine ⟨21362252214618330449294483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14241501476412220299529655 21362252214618330449294483)
    ·
      refine ⟨32043378321927495673941725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21362252214618330449294483 32043378321927495673941725)
      ·
        refine ⟨12016266870722810877728147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32043378321927495673941725 12016266870722810877728147)
        ·
          refine ⟨18024400306084216316592221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12016266870722810877728147 18024400306084216316592221)
          ·
            refine ⟨6759150114781581118722083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18024400306084216316592221 6759150114781581118722083)
            ·
              refine ⟨10138725172172371678083125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6759150114781581118722083 10138725172172371678083125)
              ·
                refine ⟨950505484891159844820293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10138725172172371678083125 950505484891159844820293)
                ·
                  refine ⟨178219778417092470903805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950505484891159844820293 178219778417092470903805)
                  ·
                    rfl

theorem cell20_390467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 1, 5, 4].length) (baseStart_390467 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390467 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390467 prefixEnd_390467 := by exact prefixLift 390467
  have htrace : WordTrace (prefixWord ++ tailWord_390467) baseStart_390467 baseEnd_390467 := by
    simpa [prefixWord, tailWord_390467, baseEnd_390467] using wordTrace_append hprefix tailTrace_390467
  have hstable : (prefixWord ++ tailWord_390467).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390467).length < 2 ^ (prefixWord ++ tailWord_390467).sum := by decide
  have hdescent : baseEnd_390467 < baseStart_390467 := by decide
  rcases family_descends (prefixWord ++ tailWord_390467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390484 : List Nat := [2, 4, 1, 1, 2, 1, 3, 2, 4]
def baseStart_390484 : Nat := 118140960795 + 390484 * 2 ^ 59
def prefixEnd_390484 : Nat := 4983230072969 + 3 ^ 40 * 390484 * 2
def baseEnd_390484 : Nat := 178227537680315967337069

theorem tailTrace_390484 : CollatzResearch.WordTrace tailWord_390484 prefixEnd_390484 178227537680315967337069 := by
  unfold tailWord_390484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121060758675316101449253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9494747678233754801932337 7121060758675316101449253)
  ·
    refine ⟨1335198892251621769021735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7121060758675316101449253 1335198892251621769021735)
    ·
      refine ⟨2002798338377432653532603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1335198892251621769021735 2002798338377432653532603)
      ·
        refine ⟨3004197507566148980298905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2002798338377432653532603 3004197507566148980298905)
        ·
          refine ⟨2253148130674611735224179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3004197507566148980298905 2253148130674611735224179)
          ·
            refine ⟨3379722196011917602836269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2253148130674611735224179 3379722196011917602836269)
            ·
              refine ⟨1267395823504469101063601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3379722196011917602836269 1267395823504469101063601)
              ·
                refine ⟨950546867628351825797701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1267395823504469101063601 950546867628351825797701)
                ·
                  refine ⟨178227537680315967337069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 950546867628351825797701 178227537680315967337069)
                  ·
                    rfl

theorem cell20_390484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 3, 2, 4].length) (baseStart_390484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390484 prefixEnd_390484 := by exact prefixLift 390484
  have htrace : WordTrace (prefixWord ++ tailWord_390484) baseStart_390484 baseEnd_390484 := by
    simpa [prefixWord, tailWord_390484, baseEnd_390484] using wordTrace_append hprefix tailTrace_390484
  have hstable : (prefixWord ++ tailWord_390484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390484).length < 2 ^ (prefixWord ++ tailWord_390484).sum := by decide
  have hdescent : baseEnd_390484 < baseStart_390484 := by decide
  rcases family_descends (prefixWord ++ tailWord_390484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390501 : List Nat := [1, 3, 1, 3, 1, 2, 4, 3, 2]
def baseStart_390501 : Nat := 118140960795 + 390501 * 2 ^ 59
def prefixEnd_390501 : Nat := 4983230072969 + 3 ^ 40 * 390501 * 2
def baseEnd_390501 : Nat := 178235296943539463770333

theorem tailTrace_390501 : CollatzResearch.WordTrace tailWord_390501 prefixEnd_390501 178235296943539463770333 := by
  unfold tailWord_390501
  simp only [CollatzResearch.WordTrace]
  refine ⟨14242741558289044106267357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9495161038859362737511571 14242741558289044106267357)
  ·
    refine ⟨5341028084358391539850259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14242741558289044106267357 5341028084358391539850259)
    ·
      refine ⟨8011542126537587309775389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5341028084358391539850259 8011542126537587309775389)
      ·
        refine ⟨3004328297451595241165771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8011542126537587309775389 3004328297451595241165771)
        ·
          refine ⟨4506492446177392861748657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004328297451595241165771 4506492446177392861748657)
          ·
            refine ⟨3379869334633044646311493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506492446177392861748657 3379869334633044646311493)
            ·
              refine ⟨633725500243695871183405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3379869334633044646311493 633725500243695871183405)
              ·
                refine ⟨237647062591385951693777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633725500243695871183405 237647062591385951693777)
                ·
                  refine ⟨178235296943539463770333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237647062591385951693777 178235296943539463770333)
                  ·
                    rfl

theorem cell20_390501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2].length) (baseStart_390501 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390501 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390501 prefixEnd_390501 := by exact prefixLift 390501
  have htrace : WordTrace (prefixWord ++ tailWord_390501) baseStart_390501 baseEnd_390501 := by
    simpa [prefixWord, tailWord_390501, baseEnd_390501] using wordTrace_append hprefix tailTrace_390501
  have hstable : (prefixWord ++ tailWord_390501).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390501).length < 2 ^ (prefixWord ++ tailWord_390501).sum := by decide
  have hdescent : baseEnd_390501 < baseStart_390501 := by decide
  rcases family_descends (prefixWord ++ tailWord_390501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390512 : List Nat := [2, 1, 1, 1, 4, 2, 9]
def baseStart_390512 : Nat := 118140960795 + 390512 * 2 ^ 59
def prefixEnd_390512 : Nat := 4983230072969 + 3 ^ 40 * 390512 * 2
def baseEnd_390512 : Nat := 19804479738141368267069

theorem tailTrace_390512 : CollatzResearch.WordTrace tailWord_390512 prefixEnd_390512 19804479738141368267069 := by
  unfold tailWord_390512
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121571380624596492458895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9495428507499461989945193 7121571380624596492458895)
  ·
    refine ⟨10682357070936894738688343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7121571380624596492458895 10682357070936894738688343)
    ·
      refine ⟨16023535606405342108032515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10682357070936894738688343 16023535606405342108032515)
      ·
        refine ⟨24035303409608013162048773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16023535606405342108032515 24035303409608013162048773)
        ·
          refine ⟨4506619389301502467884145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24035303409608013162048773 4506619389301502467884145)
          ·
            refine ⟨3379964541976126850913109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4506619389301502467884145 3379964541976126850913109)
            ·
              refine ⟨19804479738141368267069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3379964541976126850913109 19804479738141368267069)
              ·
                rfl

theorem cell20_390512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 9].length) (baseStart_390512 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390512 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390512 prefixEnd_390512 := by exact prefixLift 390512
  have htrace : WordTrace (prefixWord ++ tailWord_390512) baseStart_390512 baseEnd_390512 := by
    simpa [prefixWord, tailWord_390512, baseEnd_390512] using wordTrace_append hprefix tailTrace_390512
  have hstable : (prefixWord ++ tailWord_390512).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390512).length < 2 ^ (prefixWord ++ tailWord_390512).sum := by decide
  have hdescent : baseEnd_390512 < baseStart_390512 := by decide
  rcases family_descends (prefixWord ++ tailWord_390512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390532 : List Nat := [2, 3, 2, 1, 1, 4, 3, 1, 3]
def baseStart_390532 : Nat := 118140960795 + 390532 * 2 ^ 59
def prefixEnd_390532 : Nat := 4983230072969 + 3 ^ 40 * 390532 * 2
def baseEnd_390532 : Nat := 178249446188241133736873

theorem tailTrace_390532 : CollatzResearch.WordTrace tailWord_390532 prefixEnd_390532 178249446188241133736873 := by
  unfold tailWord_390532
  simp only [CollatzResearch.WordTrace]
  refine ⟨7121936110588368200322925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9495914814117824267097233 7121936110588368200322925)
  ·
    refine ⟨2670726041470638075121097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7121936110588368200322925 2670726041470638075121097)
    ·
      refine ⟨2003044531102978556340823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2670726041470638075121097 2003044531102978556340823)
      ·
        refine ⟨3004566796654467834511235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2003044531102978556340823 3004566796654467834511235)
        ·
          refine ⟨4506850194981701751766853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3004566796654467834511235 4506850194981701751766853)
          ·
            refine ⟨845034411559069078456285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4506850194981701751766853 845034411559069078456285)
            ·
              refine ⟨316887904334650904421107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845034411559069078456285 316887904334650904421107)
              ·
                refine ⟨475331856501976356631661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 316887904334650904421107 475331856501976356631661)
                ·
                  refine ⟨178249446188241133736873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475331856501976356631661 178249446188241133736873)
                  ·
                    rfl

theorem cell20_390532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 1, 3].length) (baseStart_390532 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390532 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390532 prefixEnd_390532 := by exact prefixLift 390532
  have htrace : WordTrace (prefixWord ++ tailWord_390532) baseStart_390532 baseEnd_390532 := by
    simpa [prefixWord, tailWord_390532, baseEnd_390532] using wordTrace_append hprefix tailTrace_390532
  have hstable : (prefixWord ++ tailWord_390532).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390532).length < 2 ^ (prefixWord ++ tailWord_390532).sum := by decide
  have hdescent : baseEnd_390532 < baseStart_390532 := by decide
  rcases family_descends (prefixWord ++ tailWord_390532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390542 : List Nat := [4, 1, 1, 4, 3, 1, 2, 4]
def baseStart_390542 : Nat := 118140960795 + 390542 * 2 ^ 59
def prefixEnd_390542 : Nat := 4983230072969 + 3 ^ 40 * 390542 * 2
def baseEnd_390542 : Nat := 59418003486908514467833

theorem tailTrace_390542 : CollatzResearch.WordTrace tailWord_390542 prefixEnd_390542 59418003486908514467833 := by
  unfold tailWord_390542
  simp only [CollatzResearch.WordTrace]
  refine ⟨1780529618892563513563735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9496157967427005405673253 1780529618892563513563735)
  ·
    refine ⟨2670794428338845270345603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1780529618892563513563735 2670794428338845270345603)
    ·
      refine ⟨4006191642508267905518405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2670794428338845270345603 4006191642508267905518405)
      ·
        refine ⟨751160932970300232284701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4006191642508267905518405 751160932970300232284701)
        ·
          refine ⟨281685349863862587106763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 751160932970300232284701 281685349863862587106763)
          ·
            refine ⟨422528024795793880660145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281685349863862587106763 422528024795793880660145)
            ·
              refine ⟨316896018596845410495109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422528024795793880660145 316896018596845410495109)
              ·
                refine ⟨59418003486908514467833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 316896018596845410495109 59418003486908514467833)
                ·
                  rfl

theorem cell20_390542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_390542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390542 prefixEnd_390542 := by exact prefixLift 390542
  have htrace : WordTrace (prefixWord ++ tailWord_390542) baseStart_390542 baseEnd_390542 := by
    simpa [prefixWord, tailWord_390542, baseEnd_390542] using wordTrace_append hprefix tailTrace_390542
  have hstable : (prefixWord ++ tailWord_390542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390542).length < 2 ^ (prefixWord ++ tailWord_390542).sum := by decide
  have hdescent : baseEnd_390542 < baseStart_390542 := by decide
  rcases family_descends (prefixWord ++ tailWord_390542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390573 : List Nat := [1, 5, 2, 2, 1, 2, 3, 2, 2]
def baseStart_390573 : Nat := 118140960795 + 390573 * 2 ^ 59
def prefixEnd_390573 : Nat := 4983230072969 + 3 ^ 40 * 390573 * 2
def baseEnd_390573 : Nat := 178268159705427213370039

theorem tailTrace_390573 : CollatzResearch.WordTrace tailWord_390573 prefixEnd_390573 178268159705427213370039 := by
  unfold tailWord_390573
  simp only [CollatzResearch.WordTrace]
  refine ⟨14245367614028200402888373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9496911742685466935258915 14245367614028200402888373)
  ·
    refine ⟨1335503213815143787770785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14245367614028200402888373 1335503213815143787770785)
    ·
      refine ⟨1001627410361357840828089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1335503213815143787770785 1001627410361357840828089)
      ·
        refine ⟨751220557771018380621067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1001627410361357840828089 751220557771018380621067)
        ·
          refine ⟨1126830836656527570931601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751220557771018380621067 1126830836656527570931601)
          ·
            refine ⟨845123127492395678198701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1126830836656527570931601 845123127492395678198701)
            ·
              refine ⟨316921172809648379324513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845123127492395678198701 316921172809648379324513)
              ·
                refine ⟨237690879607236284493385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 316921172809648379324513 237690879607236284493385)
                ·
                  refine ⟨178268159705427213370039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237690879607236284493385 178268159705427213370039)
                  ·
                    rfl

theorem cell20_390573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 3, 2, 2].length) (baseStart_390573 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390573 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390573 prefixEnd_390573 := by exact prefixLift 390573
  have htrace : WordTrace (prefixWord ++ tailWord_390573) baseStart_390573 baseEnd_390573 := by
    simpa [prefixWord, tailWord_390573, baseEnd_390573] using wordTrace_append hprefix tailTrace_390573
  have hstable : (prefixWord ++ tailWord_390573).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390573).length < 2 ^ (prefixWord ++ tailWord_390573).sum := by decide
  have hdescent : baseEnd_390573 < baseStart_390573 := by decide
  rcases family_descends (prefixWord ++ tailWord_390573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390629 : List Nat := [1, 3, 1, 5, 1, 1, 1, 4, 3]
def baseStart_390629 : Nat := 118140960795 + 390629 * 2 ^ 59
def prefixEnd_390629 : Nat := 4983230072969 + 3 ^ 40 * 390629 * 2
def baseEnd_390629 : Nat := 178293719631339907503143

theorem tailTrace_390629 : CollatzResearch.WordTrace tailWord_390629 prefixEnd_390629 178293719631339907503143 := by
  unfold tailWord_390629
  simp only [CollatzResearch.WordTrace]
  refine ⟨14247410101825321966926941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9498273401216881311284627 14247410101825321966926941)
  ·
    refine ⟨5342778788184495737597603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14247410101825321966926941 5342778788184495737597603)
    ·
      refine ⟨8014168182276743606396405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5342778788184495737597603 8014168182276743606396405)
      ·
        refine ⟨751328267088444713099663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8014168182276743606396405 751328267088444713099663)
        ·
          refine ⟨1126992400632667069649495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751328267088444713099663 1126992400632667069649495)
          ·
            refine ⟨1690488600949000604474243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1126992400632667069649495 1690488600949000604474243)
            ·
              refine ⟨2535732901423500906711365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1690488600949000604474243 2535732901423500906711365)
              ·
                refine ⟨475449919016906420008381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2535732901423500906711365 475449919016906420008381)
                ·
                  refine ⟨178293719631339907503143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475449919016906420008381 178293719631339907503143)
                  ·
                    rfl

theorem cell20_390629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 1, 4, 3].length) (baseStart_390629 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390629 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390629 prefixEnd_390629 := by exact prefixLift 390629
  have htrace : WordTrace (prefixWord ++ tailWord_390629) baseStart_390629 baseEnd_390629 := by
    simpa [prefixWord, tailWord_390629, baseEnd_390629] using wordTrace_append hprefix tailTrace_390629
  have hstable : (prefixWord ++ tailWord_390629).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390629).length < 2 ^ (prefixWord ++ tailWord_390629).sum := by decide
  have hdescent : baseEnd_390629 < baseStart_390629 := by decide
  rcases family_descends (prefixWord ++ tailWord_390629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390633 : List Nat := [1, 2, 1, 1, 1, 2, 1, 2, 9]
def baseStart_390633 : Nat := 118140960795 + 390633 * 2 ^ 59
def prefixEnd_390633 : Nat := 4983230072969 + 3 ^ 40 * 390633 * 2
def baseEnd_390633 : Nat := 178295545340333671369793

theorem tailTrace_390633 : CollatzResearch.WordTrace tailWord_390633 prefixEnd_390633 178295545340333671369793 := by
  unfold tailWord_390633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14247555993810830650072553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9498370662540553766715035 14247555993810830650072553)
  ·
    refine ⟨10685666995358122987554415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14247555993810830650072553 10685666995358122987554415)
    ·
      refine ⟨16028500493037184481331623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10685666995358122987554415 16028500493037184481331623)
      ·
        refine ⟨24042750739555776721997435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16028500493037184481331623 24042750739555776721997435)
        ·
          refine ⟨36064126109333665082996153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24042750739555776721997435 36064126109333665082996153)
          ·
            refine ⟨27048094582000248812247115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36064126109333665082996153 27048094582000248812247115)
            ·
              refine ⟨40572141873000373218370673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27048094582000248812247115 40572141873000373218370673)
              ·
                refine ⟨30429106404750279913778005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40572141873000373218370673 30429106404750279913778005)
                ·
                  refine ⟨178295545340333671369793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30429106404750279913778005 178295545340333671369793)
                  ·
                    rfl

theorem cell20_390633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 2, 9].length) (baseStart_390633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390633 prefixEnd_390633 := by exact prefixLift 390633
  have htrace : WordTrace (prefixWord ++ tailWord_390633) baseStart_390633 baseEnd_390633 := by
    simpa [prefixWord, tailWord_390633, baseEnd_390633] using wordTrace_append hprefix tailTrace_390633
  have hstable : (prefixWord ++ tailWord_390633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390633).length < 2 ^ (prefixWord ++ tailWord_390633).sum := by decide
  have hdescent : baseEnd_390633 < baseStart_390633 := by decide
  rcases family_descends (prefixWord ++ tailWord_390633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390650 : List Nat := [3, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_390650 : Nat := 118140960795 + 390650 * 2 ^ 59
def prefixEnd_390650 : Nat := 4983230072969 + 3 ^ 40 * 390650 * 2
def baseEnd_390650 : Nat := 178303304603557167803057

theorem tailTrace_390650 : CollatzResearch.WordTrace tailWord_390650 prefixEnd_390650 178303304603557167803057 := by
  unfold tailWord_390650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3562044008687310638360351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9498784023166161702294269 3562044008687310638360351)
  ·
    refine ⟨5343066013030965957540527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3562044008687310638360351 5343066013030965957540527)
    ·
      refine ⟨8014599019546448936310791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5343066013030965957540527 8014599019546448936310791)
      ·
        refine ⟨12021898529319673404466187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8014599019546448936310791 12021898529319673404466187)
        ·
          refine ⟨18032847793979510106699281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12021898529319673404466187 18032847793979510106699281)
          ·
            refine ⟨13524635845484632580024461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18032847793979510106699281 13524635845484632580024461)
            ·
              refine ⟨5071738442056737217509173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13524635845484632580024461 5071738442056737217509173)
              ·
                refine ⟨475475478942819114141485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5071738442056737217509173 475475478942819114141485)
                ·
                  refine ⟨178303304603557167803057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475475478942819114141485 178303304603557167803057)
                  ·
                    rfl

theorem cell20_390650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_390650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390650 prefixEnd_390650 := by exact prefixLift 390650
  have htrace : WordTrace (prefixWord ++ tailWord_390650) baseStart_390650 baseEnd_390650 := by
    simpa [prefixWord, tailWord_390650, baseEnd_390650] using wordTrace_append hprefix tailTrace_390650
  have hstable : (prefixWord ++ tailWord_390650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390650).length < 2 ^ (prefixWord ++ tailWord_390650).sum := by decide
  have hdescent : baseEnd_390650 < baseStart_390650 := by decide
  rcases family_descends (prefixWord ++ tailWord_390650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390664 : List Nat := [2, 1, 3, 2, 1, 1, 2, 8]
def baseStart_390664 : Nat := 118140960795 + 390664 * 2 ^ 59
def prefixEnd_390664 : Nat := 4983230072969 + 3 ^ 40 * 390664 * 2
def baseEnd_390664 : Nat := 59436564861678447112111

theorem tailTrace_390664 : CollatzResearch.WordTrace tailWord_390664 prefixEnd_390664 59436564861678447112111 := by
  unfold tailWord_390664
  simp only [CollatzResearch.WordTrace]
  refine ⟨7124343328349261472225523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9499124437799015296300697 7124343328349261472225523)
  ·
    refine ⟨10686514992523892208338285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7124343328349261472225523 10686514992523892208338285)
    ·
      refine ⟨4007443122196459578126857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10686514992523892208338285 4007443122196459578126857)
      ·
        refine ⟨3005582341647344683595143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007443122196459578126857 3005582341647344683595143)
        ·
          refine ⟨4508373512471017025392715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3005582341647344683595143 4508373512471017025392715)
          ·
            refine ⟨6762560268706525538089073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4508373512471017025392715 6762560268706525538089073)
            ·
              refine ⟨5071920201529894153566805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6762560268706525538089073 5071920201529894153566805)
              ·
                refine ⟨59436564861678447112111, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5071920201529894153566805 59436564861678447112111)
                ·
                  rfl

theorem cell20_390664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 8].length) (baseStart_390664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390664 prefixEnd_390664 := by exact prefixLift 390664
  have htrace : WordTrace (prefixWord ++ tailWord_390664) baseStart_390664 baseEnd_390664 := by
    simpa [prefixWord, tailWord_390664, baseEnd_390664] using wordTrace_append hprefix tailTrace_390664
  have hstable : (prefixWord ++ tailWord_390664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390664).length < 2 ^ (prefixWord ++ tailWord_390664).sum := by decide
  have hdescent : baseEnd_390664 < baseStart_390664 := by decide
  rcases family_descends (prefixWord ++ tailWord_390664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390670 : List Nat := [4, 1, 1, 2, 4, 1, 2, 3, 2]
def baseStart_390670 : Nat := 118140960795 + 390670 * 2 ^ 59
def prefixEnd_390670 : Nat := 4983230072969 + 3 ^ 40 * 390670 * 2
def baseEnd_390670 : Nat := 178312433148525987136309

theorem tailTrace_390670 : CollatzResearch.WordTrace tailWord_390670 prefixEnd_390670 178312433148525987136309 := by
  unfold tailWord_390670
  simp only [CollatzResearch.WordTrace]
  refine ⟨1781113186834598246146183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9499270329784523979446309 1781113186834598246146183)
  ·
    refine ⟨2671669780251897369219275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1781113186834598246146183 2671669780251897369219275)
    ·
      refine ⟨4007504670377846053828913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2671669780251897369219275 4007504670377846053828913)
      ·
        refine ⟨3005628502783384540371685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4007504670377846053828913 3005628502783384540371685)
        ·
          refine ⟨563555344271884601319691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3005628502783384540371685 563555344271884601319691)
          ·
            refine ⟨845333016407826901979537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563555344271884601319691 845333016407826901979537)
            ·
              refine ⟨633999762305870176484653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845333016407826901979537 633999762305870176484653)
              ·
                refine ⟨237749910864701316181745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 633999762305870176484653 237749910864701316181745)
                ·
                  refine ⟨178312433148525987136309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237749910864701316181745 178312433148525987136309)
                  ·
                    rfl

theorem cell20_390670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 3, 2].length) (baseStart_390670 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390670 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390670 prefixEnd_390670 := by exact prefixLift 390670
  have htrace : WordTrace (prefixWord ++ tailWord_390670) baseStart_390670 baseEnd_390670 := by
    simpa [prefixWord, tailWord_390670, baseEnd_390670] using wordTrace_append hprefix tailTrace_390670
  have hstable : (prefixWord ++ tailWord_390670).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390670).length < 2 ^ (prefixWord ++ tailWord_390670).sum := by decide
  have hdescent : baseEnd_390670 < baseStart_390670 := by decide
  rcases family_descends (prefixWord ++ tailWord_390670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390719 : List Nat := [1, 1, 2, 2, 3, 3, 4, 4]
def baseStart_390719 : Nat := 118140960795 + 390719 * 2 ^ 59
def prefixEnd_390719 : Nat := 4983230072969 + 3 ^ 40 * 390719 * 2
def baseEnd_390719 : Nat := 59444932694566531500925

theorem tailTrace_390719 : CollatzResearch.WordTrace tailWord_390719 prefixEnd_390719 59444932694566531500925 := by
  unfold tailWord_390719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14250692671499267337703211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9500461780999511558468807 14250692671499267337703211)
  ·
    refine ⟨21376039007248901006554817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14250692671499267337703211 21376039007248901006554817)
    ·
      refine ⟨16032029255436675754916113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21376039007248901006554817 16032029255436675754916113)
      ·
        refine ⟨12024021941577506816187085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16032029255436675754916113 12024021941577506816187085)
        ·
          refine ⟨4509008228091565056070157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12024021941577506816187085 4509008228091565056070157)
          ·
            refine ⟨1690878085534336896026309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4509008228091565056070157 1690878085534336896026309)
            ·
              refine ⟨317039641037688168004933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1690878085534336896026309 317039641037688168004933)
              ·
                refine ⟨59444932694566531500925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317039641037688168004933 59444932694566531500925)
                ·
                  rfl

theorem cell20_390719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 4].length) (baseStart_390719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390719 prefixEnd_390719 := by exact prefixLift 390719
  have htrace : WordTrace (prefixWord ++ tailWord_390719) baseStart_390719 baseEnd_390719 := by
    simpa [prefixWord, tailWord_390719, baseEnd_390719] using wordTrace_append hprefix tailTrace_390719
  have hstable : (prefixWord ++ tailWord_390719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390719).length < 2 ^ (prefixWord ++ tailWord_390719).sum := by decide
  have hdescent : baseEnd_390719 < baseStart_390719 := by decide
  rcases family_descends (prefixWord ++ tailWord_390719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390742 : List Nat := [5, 2, 2, 2, 2, 1, 1, 1, 4]
def baseStart_390742 : Nat := 118140960795 + 390742 * 2 ^ 59
def prefixEnd_390742 : Nat := 4983230072969 + 3 ^ 40 * 390742 * 2
def baseEnd_390742 : Nat := 178345295910413736736015

theorem tailTrace_390742 : CollatzResearch.WordTrace tailWord_390742 prefixEnd_390742 178345295910413736736015 := by
  unfold tailWord_390742
  simp only [CollatzResearch.WordTrace]
  refine ⟨890720721900996391611905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9501021033610628177193653 890720721900996391611905)
  ·
    refine ⟨668040541425747293708929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 890720721900996391611905 668040541425747293708929)
    ·
      refine ⟨501030406069310470281697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 668040541425747293708929 501030406069310470281697)
      ·
        refine ⟨375772804551982852711273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 501030406069310470281697 375772804551982852711273)
        ·
          refine ⟨281829603413987139533455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 375772804551982852711273 281829603413987139533455)
          ·
            refine ⟨422744405120980709300183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 281829603413987139533455 422744405120980709300183)
            ·
              refine ⟨634116607681471063950275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422744405120980709300183 634116607681471063950275)
              ·
                refine ⟨951174911522206595925413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634116607681471063950275 951174911522206595925413)
                ·
                  refine ⟨178345295910413736736015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951174911522206595925413 178345295910413736736015)
                  ·
                    rfl

theorem cell20_390742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 2, 1, 1, 1, 4].length) (baseStart_390742 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390742 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390742 prefixEnd_390742 := by exact prefixLift 390742
  have htrace : WordTrace (prefixWord ++ tailWord_390742) baseStart_390742 baseEnd_390742 := by
    simpa [prefixWord, tailWord_390742, baseEnd_390742] using wordTrace_append hprefix tailTrace_390742
  have hstable : (prefixWord ++ tailWord_390742).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390742).length < 2 ^ (prefixWord ++ tailWord_390742).sum := by decide
  have hdescent : baseEnd_390742 < baseStart_390742 := by decide
  rcases family_descends (prefixWord ++ tailWord_390742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390757 : List Nat := [1, 3, 1, 3, 3, 2, 2, 5]
def baseStart_390757 : Nat := 118140960795 + 390757 * 2 ^ 59
def prefixEnd_390757 : Nat := 4983230072969 + 3 ^ 40 * 390757 * 2
def baseEnd_390757 : Nat := 59450714106380117078651

theorem tailTrace_390757 : CollatzResearch.WordTrace tailWord_390757 prefixEnd_390757 59450714106380117078651 := by
  unfold tailWord_390757
  simp only [CollatzResearch.WordTrace]
  refine ⟨14252078645361599827586525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9501385763574399885057683 14252078645361599827586525)
  ·
    refine ⟨5344529492010599935344947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14252078645361599827586525 5344529492010599935344947)
    ·
      refine ⟨8016794238015899903017421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5344529492010599935344947 8016794238015899903017421)
      ·
        refine ⟨3006297839255962463631533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8016794238015899903017421 3006297839255962463631533)
        ·
          refine ⟨1127361689720985923861825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3006297839255962463631533 1127361689720985923861825)
          ·
            refine ⟨845521267290739442896369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1127361689720985923861825 845521267290739442896369)
            ·
              refine ⟨634140950468054582172277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 845521267290739442896369 634140950468054582172277)
              ·
                refine ⟨59450714106380117078651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 634140950468054582172277 59450714106380117078651)
                ·
                  rfl

theorem cell20_390757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 5].length) (baseStart_390757 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390757 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390757 prefixEnd_390757 := by exact prefixLift 390757
  have htrace : WordTrace (prefixWord ++ tailWord_390757) baseStart_390757 baseEnd_390757 := by
    simpa [prefixWord, tailWord_390757, baseEnd_390757] using wordTrace_append hprefix tailTrace_390757
  have hstable : (prefixWord ++ tailWord_390757).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390757).length < 2 ^ (prefixWord ++ tailWord_390757).sum := by decide
  have hdescent : baseEnd_390757 < baseStart_390757 := by decide
  rcases family_descends (prefixWord ++ tailWord_390757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390760 : List Nat := [2, 1, 4, 3, 1, 1, 4, 1, 3]
def baseStart_390760 : Nat := 118140960795 + 390760 * 2 ^ 59
def prefixEnd_390760 : Nat := 4983230072969 + 3 ^ 40 * 390760 * 2
def baseEnd_390760 : Nat := 178353511600885674135941

theorem tailTrace_390760 : CollatzResearch.WordTrace tailWord_390760 prefixEnd_390760 178353511600885674135941 := by
  unfold tailWord_390760
  simp only [CollatzResearch.WordTrace]
  refine ⟨7126094032175365669972867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9501458709567154226630489 7126094032175365669972867)
  ·
    refine ⟨10689141048263048504959301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7126094032175365669972867 10689141048263048504959301)
    ·
      refine ⟨2004213946549321594679869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10689141048263048504959301 2004213946549321594679869)
      ·
        refine ⟨751580229955995598004951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2004213946549321594679869 751580229955995598004951)
        ·
          refine ⟨1127370344933993397007427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 751580229955995598004951 1127370344933993397007427)
          ·
            refine ⟨1691055517400990095511141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127370344933993397007427 1691055517400990095511141)
            ·
              refine ⟨317072909512685642908339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1691055517400990095511141 317072909512685642908339)
              ·
                refine ⟨475609364269028464362509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317072909512685642908339 475609364269028464362509)
                ·
                  refine ⟨178353511600885674135941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475609364269028464362509 178353511600885674135941)
                  ·
                    rfl

theorem cell20_390760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 4, 1, 3].length) (baseStart_390760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390760 prefixEnd_390760 := by exact prefixLift 390760
  have htrace : WordTrace (prefixWord ++ tailWord_390760) baseStart_390760 baseEnd_390760 := by
    simpa [prefixWord, tailWord_390760, baseEnd_390760] using wordTrace_append hprefix tailTrace_390760
  have hstable : (prefixWord ++ tailWord_390760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390760).length < 2 ^ (prefixWord ++ tailWord_390760).sum := by decide
  have hdescent : baseEnd_390760 < baseStart_390760 := by decide
  rcases family_descends (prefixWord ++ tailWord_390760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390812 : List Nat := [2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_390812 : Nat := 118140960795 + 390812 * 2 ^ 59
def prefixEnd_390812 : Nat := 4983230072969 + 3 ^ 40 * 390812 * 2
def baseEnd_390812 : Nat := 59459081939268201467465

theorem tailTrace_390812 : CollatzResearch.WordTrace tailWord_390812 prefixEnd_390812 59459081939268201467465 := by
  unfold tailWord_390812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7127042330081172110419345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9502723106774896147225793 7127042330081172110419345)
  ·
    refine ⟨5345281747560879082814509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7127042330081172110419345 5345281747560879082814509)
    ·
      refine ⟨2004480655335329656055441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5345281747560879082814509 2004480655335329656055441)
      ·
        refine ⟨1503360491501497242041581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2004480655335329656055441 1503360491501497242041581)
        ·
          refine ⟨563760184313061465765593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1503360491501497242041581 563760184313061465765593)
          ·
            refine ⟨422820138234796099324195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563760184313061465765593 422820138234796099324195)
            ·
              refine ⟨634230207352194148986293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422820138234796099324195 634230207352194148986293)
              ·
                refine ⟨59459081939268201467465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 634230207352194148986293 59459081939268201467465)
                ·
                  rfl

theorem cell20_390812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_390812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390812 prefixEnd_390812 := by exact prefixLift 390812
  have htrace : WordTrace (prefixWord ++ tailWord_390812) baseStart_390812 baseEnd_390812 := by
    simpa [prefixWord, tailWord_390812, baseEnd_390812] using wordTrace_append hprefix tailTrace_390812
  have hstable : (prefixWord ++ tailWord_390812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390812).length < 2 ^ (prefixWord ++ tailWord_390812).sum := by decide
  have hdescent : baseEnd_390812 < baseStart_390812 := by decide
  rcases family_descends (prefixWord ++ tailWord_390812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390870 : List Nat := [5, 2, 1, 3, 1, 1, 3, 1, 3]
def baseStart_390870 : Nat := 118140960795 + 390870 * 2 ^ 59
def prefixEnd_390870 : Nat := 4983230072969 + 3 ^ 40 * 390870 * 2
def baseEnd_390870 : Nat := 178403718598214180468825

theorem tailTrace_390870 : CollatzResearch.WordTrace tailWord_390870 prefixEnd_390870 178403718598214180468825 := by
  unfold tailWord_390870
  simp only [CollatzResearch.WordTrace]
  refine ⟨891012505872013757903129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9504133395968146750966709 891012505872013757903129)
  ·
    refine ⟨668259379404010318427347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 891012505872013757903129 668259379404010318427347)
    ·
      refine ⟨1002389069106015477641021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 668259379404010318427347 1002389069106015477641021)
      ·
        refine ⟨375895900914755804115383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1002389069106015477641021 375895900914755804115383)
        ·
          refine ⟨563843851372133706173075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 375895900914755804115383 563843851372133706173075)
          ·
            refine ⟨845765777058200559259613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 563843851372133706173075 845765777058200559259613)
            ·
              refine ⟨317162166396825209722355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 845765777058200559259613 317162166396825209722355)
              ·
                refine ⟨475743249595237814583533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317162166396825209722355 475743249595237814583533)
                ·
                  refine ⟨178403718598214180468825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475743249595237814583533 178403718598214180468825)
                  ·
                    rfl

theorem cell20_390870_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_390870 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390870 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390870 prefixEnd_390870 := by exact prefixLift 390870
  have htrace : WordTrace (prefixWord ++ tailWord_390870) baseStart_390870 baseEnd_390870 := by
    simpa [prefixWord, tailWord_390870, baseEnd_390870] using wordTrace_append hprefix tailTrace_390870
  have hstable : (prefixWord ++ tailWord_390870).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390870).length < 2 ^ (prefixWord ++ tailWord_390870).sum := by decide
  have hdescent : baseEnd_390870 < baseStart_390870 := by decide
  rcases family_descends (prefixWord ++ tailWord_390870) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390885 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 4]
def baseStart_390885 : Nat := 118140960795 + 390885 * 2 ^ 59
def prefixEnd_390885 : Nat := 4983230072969 + 3 ^ 40 * 390885 * 2
def baseEnd_390885 : Nat := 178410565006940794968763

theorem tailTrace_390885 : CollatzResearch.WordTrace tailWord_390885 prefixEnd_390885 178410565006940794968763 := by
  unfold tailWord_390885
  simp only [CollatzResearch.WordTrace]
  refine ⟨14256747188897877688246109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9504498125931918458830739 14256747188897877688246109)
  ·
    refine ⟨5346280195836704133092291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14256747188897877688246109 5346280195836704133092291)
    ·
      refine ⟨8019420293755056199638437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5346280195836704133092291 8019420293755056199638437)
      ·
        refine ⟨1503641305079073037432207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8019420293755056199638437 1503641305079073037432207)
        ·
          refine ⟨2255461957618609556148311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503641305079073037432207 2255461957618609556148311)
          ·
            refine ⟨3383192936427914334222467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2255461957618609556148311 3383192936427914334222467)
            ·
              refine ⟨5074789404641871501333701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3383192936427914334222467 5074789404641871501333701)
              ·
                refine ⟨951523013370350906500069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5074789404641871501333701 951523013370350906500069)
                ·
                  refine ⟨178410565006940794968763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951523013370350906500069 178410565006940794968763)
                  ·
                    rfl

theorem cell20_390885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 4].length) (baseStart_390885 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390885 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390885 prefixEnd_390885 := by exact prefixLift 390885
  have htrace : WordTrace (prefixWord ++ tailWord_390885) baseStart_390885 baseEnd_390885 := by
    simpa [prefixWord, tailWord_390885, baseEnd_390885] using wordTrace_append hprefix tailTrace_390885
  have hstable : (prefixWord ++ tailWord_390885).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390885).length < 2 ^ (prefixWord ++ tailWord_390885).sum := by decide
  have hdescent : baseEnd_390885 < baseStart_390885 := by decide
  rcases family_descends (prefixWord ++ tailWord_390885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390888 : List Nat := [2, 1, 4, 1, 3, 3, 2, 4]
def baseStart_390888 : Nat := 118140960795 + 390888 * 2 ^ 59
def prefixEnd_390888 : Nat := 4983230072969 + 3 ^ 40 * 390888 * 2
def baseEnd_390888 : Nat := 59470644762895372622917

theorem tailTrace_390888 : CollatzResearch.WordTrace tailWord_390888 prefixEnd_390888 59470644762895372622917 := by
  unfold tailWord_390888
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128428303943504600302659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9504571071924672800403545 7128428303943504600302659)
  ·
    refine ⟨10692642455915256900453989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7128428303943504600302659 10692642455915256900453989)
    ·
      refine ⟨2004870460484110668835123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10692642455915256900453989 2004870460484110668835123)
      ·
        refine ⟨3007305690726166003252685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2004870460484110668835123 3007305690726166003252685)
        ·
          refine ⟨1127739634022312251219757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3007305690726166003252685 1127739634022312251219757)
          ·
            refine ⟨422902362758367094207409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1127739634022312251219757 422902362758367094207409)
            ·
              refine ⟨317176772068775320655557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 422902362758367094207409 317176772068775320655557)
              ·
                refine ⟨59470644762895372622917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317176772068775320655557 59470644762895372622917)
                ·
                  rfl

theorem cell20_390888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 4].length) (baseStart_390888 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390888 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390888 prefixEnd_390888 := by exact prefixLift 390888
  have htrace : WordTrace (prefixWord ++ tailWord_390888) baseStart_390888 baseEnd_390888 := by
    simpa [prefixWord, tailWord_390888, baseEnd_390888] using wordTrace_append hprefix tailTrace_390888
  have hstable : (prefixWord ++ tailWord_390888).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390888).length < 2 ^ (prefixWord ++ tailWord_390888).sum := by decide
  have hdescent : baseEnd_390888 < baseStart_390888 := by decide
  rcases family_descends (prefixWord ++ tailWord_390888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390899 : List Nat := [1, 1, 1, 2, 2, 3, 3, 2, 5]
def baseStart_390899 : Nat := 118140960795 + 390899 * 2 ^ 59
def prefixEnd_390899 : Nat := 4983230072969 + 3 ^ 40 * 390899 * 2
def baseEnd_390899 : Nat := 178416954988418968502039

theorem tailTrace_390899 : CollatzResearch.WordTrace tailWord_390899 prefixEnd_390899 178416954988418968502039 := by
  unfold tailWord_390899
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257257810847158079255751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9504838540564772052837167 14257257810847158079255751)
  ·
    refine ⟨21385886716270737118883627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257257810847158079255751 21385886716270737118883627)
    ·
      refine ⟨32078830074406105678325441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21385886716270737118883627 32078830074406105678325441)
      ·
        refine ⟨24059122555804579258744081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32078830074406105678325441 24059122555804579258744081)
        ·
          refine ⟨18044341916853434444058061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24059122555804579258744081 18044341916853434444058061)
          ·
            refine ⟨6766628218820037916521773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 18044341916853434444058061 6766628218820037916521773)
            ·
              refine ⟨2537485582057514218695665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6766628218820037916521773 2537485582057514218695665)
              ·
                refine ⟨1903114186543135664021749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2537485582057514218695665 1903114186543135664021749)
                ·
                  refine ⟨178416954988418968502039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1903114186543135664021749 178416954988418968502039)
                  ·
                    rfl

theorem cell20_390899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 3, 2, 5].length) (baseStart_390899 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390899 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390899 prefixEnd_390899 := by exact prefixLift 390899
  have htrace : WordTrace (prefixWord ++ tailWord_390899) baseStart_390899 baseEnd_390899 := by
    simpa [prefixWord, tailWord_390899, baseEnd_390899] using wordTrace_append hprefix tailTrace_390899
  have hstable : (prefixWord ++ tailWord_390899).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390899).length < 2 ^ (prefixWord ++ tailWord_390899).sum := by decide
  have hdescent : baseEnd_390899 < baseStart_390899 := by decide
  rcases family_descends (prefixWord ++ tailWord_390899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390916 : List Nat := [2, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_390916 : Nat := 118140960795 + 390916 * 2 ^ 59
def prefixEnd_390916 : Nat := 4983230072969 + 3 ^ 40 * 390916 * 2
def baseEnd_390916 : Nat := 178424714251642464935303

theorem tailTrace_390916 : CollatzResearch.WordTrace tailWord_390916 prefixEnd_390916 178424714251642464935303 := by
  unfold tailWord_390916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7128938925892784991312301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9505251901190379988416401 7128938925892784991312301)
  ·
    refine ⟨2673352097209794371742113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7128938925892784991312301 2673352097209794371742113)
    ·
      refine ⟨2005014072907345778806585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2673352097209794371742113 2005014072907345778806585)
      ·
        refine ⟨1503760554680509334104939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005014072907345778806585 1503760554680509334104939)
        ·
          refine ⟨2255640832020764001157409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1503760554680509334104939 2255640832020764001157409)
          ·
            refine ⟨1691730624015573000868057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2255640832020764001157409 1691730624015573000868057)
            ·
              refine ⟨1268797968011679750651043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1691730624015573000868057 1268797968011679750651043)
              ·
                refine ⟨1903196952017519625976565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1268797968011679750651043 1903196952017519625976565)
                ·
                  refine ⟨178424714251642464935303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1903196952017519625976565 178424714251642464935303)
                  ·
                    rfl

theorem cell20_390916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_390916 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390916 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390916 prefixEnd_390916 := by exact prefixLift 390916
  have htrace : WordTrace (prefixWord ++ tailWord_390916) baseStart_390916 baseEnd_390916 := by
    simpa [prefixWord, tailWord_390916, baseEnd_390916] using wordTrace_append hprefix tailTrace_390916
  have hstable : (prefixWord ++ tailWord_390916).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390916).length < 2 ^ (prefixWord ++ tailWord_390916).sum := by decide
  have hdescent : baseEnd_390916 < baseStart_390916 := by decide
  rcases family_descends (prefixWord ++ tailWord_390916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390919 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 4]
def baseStart_390919 : Nat := 118140960795 + 390919 * 2 ^ 59
def prefixEnd_390919 : Nat := 4983230072969 + 3 ^ 40 * 390919 * 2
def baseEnd_390919 : Nat := 178426083533387787835291

theorem tailTrace_390919 : CollatzResearch.WordTrace tailWord_390919 prefixEnd_390919 178426083533387787835291 := by
  unfold tailWord_390919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14257987270774701494983811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9505324847183134329989207 14257987270774701494983811)
  ·
    refine ⟨21386980906162052242475717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14257987270774701494983811 21386980906162052242475717)
    ·
      refine ⟨4010058919905384795464197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21386980906162052242475717 4010058919905384795464197)
      ·
        refine ⟨751886047482259649149537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4010058919905384795464197 751886047482259649149537)
        ·
          refine ⟨563914535611694736862153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 751886047482259649149537 563914535611694736862153)
          ·
            refine ⟨422935901708771052646615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 563914535611694736862153 422935901708771052646615)
            ·
              refine ⟨634403852563156578969923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 422935901708771052646615 634403852563156578969923)
              ·
                refine ⟨951605778844734868454885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634403852563156578969923 951605778844734868454885)
                ·
                  refine ⟨178426083533387787835291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951605778844734868454885 178426083533387787835291)
                  ·
                    rfl

theorem cell20_390919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 4].length) (baseStart_390919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390919 prefixEnd_390919 := by exact prefixLift 390919
  have htrace : WordTrace (prefixWord ++ tailWord_390919) baseStart_390919 baseEnd_390919 := by
    simpa [prefixWord, tailWord_390919, baseEnd_390919] using wordTrace_append hprefix tailTrace_390919
  have hstable : (prefixWord ++ tailWord_390919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390919).length < 2 ^ (prefixWord ++ tailWord_390919).sum := by decide
  have hdescent : baseEnd_390919 < baseStart_390919 := by decide
  rcases family_descends (prefixWord ++ tailWord_390919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390923 : List Nat := [1, 1, 1, 1, 5, 1, 5, 1, 4]
def baseStart_390923 : Nat := 118140960795 + 390923 * 2 ^ 59
def prefixEnd_390923 : Nat := 4983230072969 + 3 ^ 40 * 390923 * 2
def baseEnd_390923 : Nat := 178427909242381551701941

theorem tailTrace_390923 : CollatzResearch.WordTrace tailWord_390923 prefixEnd_390923 178427909242381551701941 := by
  unfold tailWord_390923
  simp only [CollatzResearch.WordTrace]
  refine ⟨14258133162760210178129423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9505422108506806785419615 14258133162760210178129423)
  ·
    refine ⟨21387199744140315267194135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14258133162760210178129423 21387199744140315267194135)
    ·
      refine ⟨32080799616210472900791203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21387199744140315267194135 32080799616210472900791203)
      ·
        refine ⟨48121199424315709351186805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32080799616210472900791203 48121199424315709351186805)
        ·
          refine ⟨4511362446029597751673763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 48121199424315709351186805 4511362446029597751673763)
          ·
            refine ⟨6767043669044396627510645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4511362446029597751673763 6767043669044396627510645)
            ·
              refine ⟨634410343972912183829123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6767043669044396627510645 634410343972912183829123)
              ·
                refine ⟨951615515959368275743685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634410343972912183829123 951615515959368275743685)
                ·
                  refine ⟨178427909242381551701941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 951615515959368275743685 178427909242381551701941)
                  ·
                    rfl

theorem cell20_390923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 1, 4].length) (baseStart_390923 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390923 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390923 prefixEnd_390923 := by exact prefixLift 390923
  have htrace : WordTrace (prefixWord ++ tailWord_390923) baseStart_390923 baseEnd_390923 := by
    simpa [prefixWord, tailWord_390923, baseEnd_390923] using wordTrace_append hprefix tailTrace_390923
  have hstable : (prefixWord ++ tailWord_390923).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390923).length < 2 ^ (prefixWord ++ tailWord_390923).sum := by decide
  have hdescent : baseEnd_390923 < baseStart_390923 := by decide
  rcases family_descends (prefixWord ++ tailWord_390923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390933 : List Nat := [1, 3, 2, 1, 2, 3, 4, 1, 3]
def baseStart_390933 : Nat := 118140960795 + 390933 * 2 ^ 59
def prefixEnd_390933 : Nat := 4983230072969 + 3 ^ 40 * 390933 * 2
def baseEnd_390933 : Nat := 178432473514865961368567

theorem tailTrace_390933 : CollatzResearch.WordTrace tailWord_390933 prefixEnd_390933 178432473514865961368567 := by
  unfold tailWord_390933
  simp only [CollatzResearch.WordTrace]
  refine ⟨14258497892723981885993453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9505665261815987923995635 14258497892723981885993453)
  ·
    refine ⟨5346936709771493207247545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14258497892723981885993453 5346936709771493207247545)
    ·
      refine ⟨4010202532328619905435659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5346936709771493207247545 4010202532328619905435659)
      ·
        refine ⟨6015303798492929858153489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4010202532328619905435659 6015303798492929858153489)
        ·
          refine ⟨4511477848869697393615117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6015303798492929858153489 4511477848869697393615117)
          ·
            refine ⟨1691804193326136522605669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4511477848869697393615117 1691804193326136522605669)
            ·
              refine ⟨317213286248650597988563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1691804193326136522605669 317213286248650597988563)
              ·
                refine ⟨475819929372975896982845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317213286248650597988563 475819929372975896982845)
                ·
                  refine ⟨178432473514865961368567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 475819929372975896982845 178432473514865961368567)
                  ·
                    rfl

theorem cell20_390933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 4, 1, 3].length) (baseStart_390933 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390933 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390933 prefixEnd_390933 := by exact prefixLift 390933
  have htrace : WordTrace (prefixWord ++ tailWord_390933) baseStart_390933 baseEnd_390933 := by
    simpa [prefixWord, tailWord_390933, baseEnd_390933] using wordTrace_append hprefix tailTrace_390933
  have hstable : (prefixWord ++ tailWord_390933).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390933).length < 2 ^ (prefixWord ++ tailWord_390933).sum := by decide
  have hdescent : baseEnd_390933 < baseStart_390933 := by decide
  rcases family_descends (prefixWord ++ tailWord_390933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_390974 : List Nat := [4, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_390974 : Nat := 118140960795 + 390974 * 2 ^ 59
def prefixEnd_390974 : Nat := 4983230072969 + 3 ^ 40 * 390974 * 2
def baseEnd_390974 : Nat := 178451187032052041001733

theorem tailTrace_390974 : CollatzResearch.WordTrace tailWord_390974 prefixEnd_390974 178451187032052041001733 := by
  unfold tailWord_390974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1782499160696930736029497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9506662190383630592157317 1782499160696930736029497)
  ·
    refine ⟨1336874370522698052022123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1782499160696930736029497 1336874370522698052022123)
    ·
      refine ⟨2005311555784047078033185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1336874370522698052022123 2005311555784047078033185)
      ·
        refine ⟨1503983666838035308524889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2005311555784047078033185 1503983666838035308524889)
        ·
          refine ⟨1127987750128526481393667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1503983666838035308524889 1127987750128526481393667)
          ·
            refine ⟨1691981625192789722090501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1127987750128526481393667 1691981625192789722090501)
            ·
              refine ⟨317246554723648072891969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1691981625192789722090501 317246554723648072891969)
              ·
                refine ⟨237934916042736054668977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317246554723648072891969 237934916042736054668977)
                ·
                  refine ⟨178451187032052041001733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 237934916042736054668977 178451187032052041001733)
                  ·
                    rfl

theorem cell20_390974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_390974 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_390974 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_390974 prefixEnd_390974 := by exact prefixLift 390974
  have htrace : WordTrace (prefixWord ++ tailWord_390974) baseStart_390974 baseEnd_390974 := by
    simpa [prefixWord, tailWord_390974, baseEnd_390974] using wordTrace_append hprefix tailTrace_390974
  have hstable : (prefixWord ++ tailWord_390974).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_390974).length < 2 ^ (prefixWord ++ tailWord_390974).sum := by decide
  have hdescent : baseEnd_390974 < baseStart_390974 := by decide
  rcases family_descends (prefixWord ++ tailWord_390974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391013 : List Nat := [1, 3, 1, 3, 1, 1, 1, 4, 5]
def baseStart_391013 : Nat := 118140960795 + 391013 * 2 ^ 59
def prefixEnd_391013 : Nat := 4983230072969 + 3 ^ 40 * 391013 * 2
def baseEnd_391013 : Nat := 178468987694741238701573

theorem tailTrace_391013 : CollatzResearch.WordTrace tailWord_391013 prefixEnd_391013 178468987694741238701573 := by
  unfold tailWord_391013
  simp only [CollatzResearch.WordTrace]
  refine ⟨14261415732434155548905693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9507610488289437032603795 14261415732434155548905693)
  ·
    refine ⟨5348030899662808330839635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14261415732434155548905693 5348030899662808330839635)
    ·
      refine ⟨8022046349494212496259453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5348030899662808330839635 8022046349494212496259453)
      ·
        refine ⟨3008267381060329686097295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8022046349494212496259453 3008267381060329686097295)
        ·
          refine ⟨4512401071590494529145943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008267381060329686097295 4512401071590494529145943)
          ·
            refine ⟨6768601607385741793718915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4512401071590494529145943 6768601607385741793718915)
            ·
              refine ⟨10152902411078612690578373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6768601607385741793718915 10152902411078612690578373)
              ·
                refine ⟨1903669202077239879483445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10152902411078612690578373 1903669202077239879483445)
                ·
                  refine ⟨178468987694741238701573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1903669202077239879483445 178468987694741238701573)
                  ·
                    rfl

theorem cell20_391013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 4, 5].length) (baseStart_391013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391013 prefixEnd_391013 := by exact prefixLift 391013
  have htrace : WordTrace (prefixWord ++ tailWord_391013) baseStart_391013 baseEnd_391013 := by
    simpa [prefixWord, tailWord_391013, baseEnd_391013] using wordTrace_append hprefix tailTrace_391013
  have hstable : (prefixWord ++ tailWord_391013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391013).length < 2 ^ (prefixWord ++ tailWord_391013).sum := by decide
  have hdescent : baseEnd_391013 < baseStart_391013 := by decide
  rcases family_descends (prefixWord ++ tailWord_391013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391068 : List Nat := [2, 2, 3, 3, 1, 1, 1, 2, 5]
def baseStart_391068 : Nat := 118140960795 + 391068 * 2 ^ 59
def prefixEnd_391068 : Nat := 4983230072969 + 3 ^ 40 * 391068 * 2
def baseEnd_391068 : Nat := 178494091193405491868015

theorem tailTrace_391068 : CollatzResearch.WordTrace tailWord_391068 prefixEnd_391068 178494091193405491868015 := by
  unfold tailWord_391068
  simp only [CollatzResearch.WordTrace]
  refine ⟨7131710873617449971078929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9508947831489933294771905 7131710873617449971078929)
  ·
    refine ⟨5348783155213087478309197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7131710873617449971078929 5348783155213087478309197)
    ·
      refine ⟨2005793683204907804365949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5348783155213087478309197 2005793683204907804365949)
      ·
        refine ⟨752172631201840426637231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2005793683204907804365949 752172631201840426637231)
        ·
          refine ⟨1128258946802760639955847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752172631201840426637231 1128258946802760639955847)
          ·
            refine ⟨1692388420204140959933771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1128258946802760639955847 1692388420204140959933771)
            ·
              refine ⟨2538582630306211439900657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1692388420204140959933771 2538582630306211439900657)
              ·
                refine ⟨1903936972729658579925493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2538582630306211439900657 1903936972729658579925493)
                ·
                  refine ⟨178494091193405491868015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1903936972729658579925493 178494091193405491868015)
                  ·
                    rfl

theorem cell20_391068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 1, 1, 2, 5].length) (baseStart_391068 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391068 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391068 prefixEnd_391068 := by exact prefixLift 391068
  have htrace : WordTrace (prefixWord ++ tailWord_391068) baseStart_391068 baseEnd_391068 := by
    simpa [prefixWord, tailWord_391068, baseEnd_391068] using wordTrace_append hprefix tailTrace_391068
  have hstable : (prefixWord ++ tailWord_391068).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391068).length < 2 ^ (prefixWord ++ tailWord_391068).sum := by decide
  have hdescent : baseEnd_391068 < baseStart_391068 := by decide
  rcases family_descends (prefixWord ++ tailWord_391068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391102 : List Nat := [4, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_391102 : Nat := 118140960795 + 391102 * 2 ^ 59
def prefixEnd_391102 : Nat := 4983230072969 + 3 ^ 40 * 391102 * 2
def baseEnd_391102 : Nat := 178509609719852484734543

theorem tailTrace_391102 : CollatzResearch.WordTrace tailWord_391102 prefixEnd_391102 178509609719852484734543 := by
  unfold tailWord_391102
  simp only [CollatzResearch.WordTrace]
  refine ⟨1783082728638965468611945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9509774552741149165930373 1783082728638965468611945)
  ·
    refine ⟨1337312046479224101458959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1783082728638965468611945 1337312046479224101458959)
    ·
      refine ⟨2005968069718836152188439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1337312046479224101458959 2005968069718836152188439)
      ·
        refine ⟨3008952104578254228282659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2005968069718836152188439 3008952104578254228282659)
        ·
          refine ⟨4513428156867381342423989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3008952104578254228282659 4513428156867381342423989)
          ·
            refine ⟨423133889706317000852249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4513428156867381342423989 423133889706317000852249)
            ·
              refine ⟨317350417279737750639187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423133889706317000852249 317350417279737750639187)
              ·
                refine ⟨476025625919606625958781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 317350417279737750639187 476025625919606625958781)
                ·
                  refine ⟨178509609719852484734543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476025625919606625958781 178509609719852484734543)
                  ·
                    rfl

theorem cell20_391102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_391102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391102 prefixEnd_391102 := by exact prefixLift 391102
  have htrace : WordTrace (prefixWord ++ tailWord_391102) baseStart_391102 baseEnd_391102 := by
    simpa [prefixWord, tailWord_391102, baseEnd_391102] using wordTrace_append hprefix tailTrace_391102
  have hstable : (prefixWord ++ tailWord_391102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391102).length < 2 ^ (prefixWord ++ tailWord_391102).sum := by decide
  have hdescent : baseEnd_391102 < baseStart_391102 := by decide
  rcases family_descends (prefixWord ++ tailWord_391102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391141 : List Nat := [1, 3, 1, 15]
def baseStart_391141 : Nat := 118140960795 + 391141 * 2 ^ 59
def prefixEnd_391141 : Nat := 4983230072969 + 3 ^ 40 * 391141 * 2
def baseEnd_391141 : Nat := 734680701162722972981

theorem tailTrace_391141 : CollatzResearch.WordTrace tailWord_391141 prefixEnd_391141 734680701162722972981 := by
  unfold tailWord_391141
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266084275970433409565277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9510722850646955606376851 14266084275970433409565277)
  ·
    refine ⟨5349781603488912528586979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14266084275970433409565277 5349781603488912528586979)
    ·
      refine ⟨8024672405233368792880469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5349781603488912528586979 8024672405233368792880469)
      ·
        refine ⟨734680701162722972981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 8024672405233368792880469 734680701162722972981)
        ·
          rfl

theorem cell20_391141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 15].length) (baseStart_391141 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391141 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391141 prefixEnd_391141 := by exact prefixLift 391141
  have htrace : WordTrace (prefixWord ++ tailWord_391141) baseStart_391141 baseEnd_391141 := by
    simpa [prefixWord, tailWord_391141, baseEnd_391141] using wordTrace_append hprefix tailTrace_391141
  have hstable : (prefixWord ++ tailWord_391141).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391141).length < 2 ^ (prefixWord ++ tailWord_391141).sum := by decide
  have hdescent : baseEnd_391141 < baseStart_391141 := by decide
  rcases family_descends (prefixWord ++ tailWord_391141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391143 : List Nat := [1, 1, 5, 2, 4, 1, 2, 2, 2]
def baseStart_391143 : Nat := 118140960795 + 391143 * 2 ^ 59
def prefixEnd_391143 : Nat := 4983230072969 + 3 ^ 40 * 391143 * 2
def baseEnd_391143 : Nat := 178528323237038564367709

theorem tailTrace_391143 : CollatzResearch.WordTrace tailWord_391143 prefixEnd_391143 178528323237038564367709 := by
  unfold tailWord_391143
  simp only [CollatzResearch.WordTrace]
  refine ⟨14266157221963187751138083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9510771481308791834092055 14266157221963187751138083)
  ·
    refine ⟨21399235832944781626707125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14266157221963187751138083 21399235832944781626707125)
    ·
      refine ⟨2006178359338573277503793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 21399235832944781626707125 2006178359338573277503793)
      ·
        refine ⟨1504633769503929958127845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2006178359338573277503793 1504633769503929958127845)
        ·
          refine ⟨282118831781986867148971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1504633769503929958127845 282118831781986867148971)
          ·
            refine ⟨423178247672980300723457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 282118831781986867148971 423178247672980300723457)
            ·
              refine ⟨317383685754735225542593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423178247672980300723457 317383685754735225542593)
              ·
                refine ⟨238037764316051419156945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 317383685754735225542593 238037764316051419156945)
                ·
                  refine ⟨178528323237038564367709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238037764316051419156945 178528323237038564367709)
                  ·
                    rfl

theorem cell20_391143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2].length) (baseStart_391143 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391143 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391143 prefixEnd_391143 := by exact prefixLift 391143
  have htrace : WordTrace (prefixWord ++ tailWord_391143) baseStart_391143 baseEnd_391143 := by
    simpa [prefixWord, tailWord_391143, baseEnd_391143] using wordTrace_append hprefix tailTrace_391143
  have hstable : (prefixWord ++ tailWord_391143).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391143).length < 2 ^ (prefixWord ++ tailWord_391143).sum := by decide
  have hdescent : baseEnd_391143 < baseStart_391143 := by decide
  rcases family_descends (prefixWord ++ tailWord_391143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391175 : List Nat := [1, 1, 4, 3, 1, 3, 3, 4]
def baseStart_391175 : Nat := 118140960795 + 391175 * 2 ^ 59
def prefixEnd_391175 : Nat := 4983230072969 + 3 ^ 40 * 391175 * 2
def baseEnd_391175 : Nat := 59514309636329558433637

theorem tailTrace_391175 : CollatzResearch.WordTrace tailWord_391175 prefixEnd_391175 59514309636329558433637 := by
  unfold tailWord_391175
  simp only [CollatzResearch.WordTrace]
  refine ⟨14267324357847257216302979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9511549571898171477535319 14267324357847257216302979)
  ·
    refine ⟨21400986536770885824454469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14267324357847257216302979 21400986536770885824454469)
    ·
      refine ⟨4012684975644541092085213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21400986536770885824454469 4012684975644541092085213)
      ·
        refine ⟨1504756865866702909531955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4012684975644541092085213 1504756865866702909531955)
        ·
          refine ⟨2257135298800054364297933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1504756865866702909531955 2257135298800054364297933)
          ·
            refine ⟨846425737050020386611725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2257135298800054364297933 846425737050020386611725)
            ·
              refine ⟨317409651393757644979397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 846425737050020386611725 317409651393757644979397)
              ·
                refine ⟨59514309636329558433637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317409651393757644979397 59514309636329558433637)
                ·
                  rfl

theorem cell20_391175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 3, 4].length) (baseStart_391175 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391175 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391175 prefixEnd_391175 := by exact prefixLift 391175
  have htrace : WordTrace (prefixWord ++ tailWord_391175) baseStart_391175 baseEnd_391175 := by
    simpa [prefixWord, tailWord_391175, baseEnd_391175] using wordTrace_append hprefix tailTrace_391175
  have hstable : (prefixWord ++ tailWord_391175).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391175).length < 2 ^ (prefixWord ++ tailWord_391175).sum := by decide
  have hdescent : baseEnd_391175 < baseStart_391175 := by decide
  rcases family_descends (prefixWord ++ tailWord_391175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391196 : List Nat := [2, 2, 3, 1, 3, 2, 7]
def baseStart_391196 : Nat := 118140960795 + 391196 * 2 ^ 59
def prefixEnd_391196 : Nat := 4983230072969 + 3 ^ 40 * 391196 * 2
def baseEnd_391196 : Nat := 19839168209022881733425

theorem tailTrace_391196 : CollatzResearch.WordTrace tailWord_391196 prefixEnd_391196 19839168209022881733425 := by
  unfold tailWord_391196
  simp only [CollatzResearch.WordTrace]
  refine ⟨7134045145385588901408721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9512060193847451868544961 7134045145385588901408721)
  ·
    refine ⟨5350533859039191676056541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7134045145385588901408721 5350533859039191676056541)
    ·
      refine ⟨2006450197139696878521203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5350533859039191676056541 2006450197139696878521203)
      ·
        refine ⟨3009675295709545317781805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2006450197139696878521203 3009675295709545317781805)
        ·
          refine ⟨1128628235891079494168177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3009675295709545317781805 1128628235891079494168177)
          ·
            refine ⟨846471176918309620626133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1128628235891079494168177 846471176918309620626133)
            ·
              refine ⟨19839168209022881733425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 846471176918309620626133 19839168209022881733425)
              ·
                rfl

theorem cell20_391196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 7].length) (baseStart_391196 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391196 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391196 prefixEnd_391196 := by exact prefixLift 391196
  have htrace : WordTrace (prefixWord ++ tailWord_391196) baseStart_391196 baseEnd_391196 := by
    simpa [prefixWord, tailWord_391196, baseEnd_391196] using wordTrace_append hprefix tailTrace_391196
  have hstable : (prefixWord ++ tailWord_391196).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391196).length < 2 ^ (prefixWord ++ tailWord_391196).sum := by decide
  have hdescent : baseEnd_391196 < baseStart_391196 := by decide
  rcases family_descends (prefixWord ++ tailWord_391196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391203 : List Nat := [1, 1, 1, 4, 3, 1, 3, 1, 5]
def baseStart_391203 : Nat := 118140960795 + 391203 * 2 ^ 59
def prefixEnd_391203 : Nat := 4983230072969 + 3 ^ 40 * 391203 * 2
def baseEnd_391203 : Nat := 178555708871945022367463

theorem tailTrace_391203 : CollatzResearch.WordTrace tailWord_391203 prefixEnd_391203 178555708871945022367463 := by
  unfold tailWord_391203
  simp only [CollatzResearch.WordTrace]
  refine ⟨14268345601745817998322263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9512230401163878665548175 14268345601745817998322263)
  ·
    refine ⟨21402518402618726997483395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14268345601745817998322263 21402518402618726997483395)
    ·
      refine ⟨32103777603928090496225093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21402518402618726997483395 32103777603928090496225093)
      ·
        refine ⟨6019458300736516968042205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32103777603928090496225093 6019458300736516968042205)
        ·
          refine ⟨2257296862776193863015827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6019458300736516968042205 2257296862776193863015827)
          ·
            refine ⟨3385945294164290794523741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2257296862776193863015827 3385945294164290794523741)
            ·
              refine ⟨1269729485311609047946403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3385945294164290794523741 1269729485311609047946403)
              ·
                refine ⟨1904594227967413571919605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1269729485311609047946403 1904594227967413571919605)
                ·
                  refine ⟨178555708871945022367463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1904594227967413571919605 178555708871945022367463)
                  ·
                    rfl

theorem cell20_391203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 3, 1, 5].length) (baseStart_391203 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391203 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391203 prefixEnd_391203 := by exact prefixLift 391203
  have htrace : WordTrace (prefixWord ++ tailWord_391203) baseStart_391203 baseEnd_391203 := by
    simpa [prefixWord, tailWord_391203, baseEnd_391203] using wordTrace_append hprefix tailTrace_391203
  have hstable : (prefixWord ++ tailWord_391203).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391203).length < 2 ^ (prefixWord ++ tailWord_391203).sum := by decide
  have hdescent : baseEnd_391203 < baseStart_391203 := by decide
  rcases family_descends (prefixWord ++ tailWord_391203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391244 : List Nat := [2, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_391244 : Nat := 118140960795 + 391244 * 2 ^ 59
def prefixEnd_391244 : Nat := 4983230072969 + 3 ^ 40 * 391244 * 2
def baseEnd_391244 : Nat := 178574422389131102000629

theorem tailTrace_391244 : CollatzResearch.WordTrace tailWord_391244 prefixEnd_391244 178574422389131102000629 := by
  unfold tailWord_391244
  simp only [CollatzResearch.WordTrace]
  refine ⟨7134920497298641000282393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9513227329731521333709857 7134920497298641000282393)
  ·
    refine ⟨5351190372973980750211795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7134920497298641000282393 5351190372973980750211795)
    ·
      refine ⟨8026785559460971125317693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5351190372973980750211795 8026785559460971125317693)
      ·
        refine ⟨3010044584797864171994135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8026785559460971125317693 3010044584797864171994135)
        ·
          refine ⟨4515066877196796257991203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3010044584797864171994135 4515066877196796257991203)
          ·
            refine ⟨6772600315795194386986805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515066877196796257991203 6772600315795194386986805)
            ·
              refine ⟨634931279605799473780013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6772600315795194386986805 634931279605799473780013)
              ·
                refine ⟨238099229852174802667505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 634931279605799473780013 238099229852174802667505)
                ·
                  refine ⟨178574422389131102000629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238099229852174802667505 178574422389131102000629)
                  ·
                    rfl

theorem cell20_391244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_391244 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391244 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391244 prefixEnd_391244 := by exact prefixLift 391244
  have htrace : WordTrace (prefixWord ++ tailWord_391244) baseStart_391244 baseEnd_391244 := by
    simpa [prefixWord, tailWord_391244, baseEnd_391244] using wordTrace_append hprefix tailTrace_391244
  have hstable : (prefixWord ++ tailWord_391244).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391244).length < 2 ^ (prefixWord ++ tailWord_391244).sum := by decide
  have hdescent : baseEnd_391244 < baseStart_391244 := by decide
  rcases family_descends (prefixWord ++ tailWord_391244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391255 : List Nat := [1, 1, 3, 2, 2, 1, 10]
def baseStart_391255 : Nat := 118140960795 + 391255 * 2 ^ 59
def prefixEnd_391255 : Nat := 4983230072969 + 3 ^ 40 * 391255 * 2
def baseEnd_391255 : Nat := 19842160343207105848213

theorem tailTrace_391255 : CollatzResearch.WordTrace tailWord_391255 prefixEnd_391255 19842160343207105848213 := by
  unfold tailWord_391255
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270242197557430879215219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9513494798371620586143479 14270242197557430879215219)
  ·
    refine ⟨21405363296336146318822829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14270242197557430879215219 21405363296336146318822829)
    ·
      refine ⟨8027011236126054869558561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21405363296336146318822829 8027011236126054869558561)
      ·
        refine ⟨6020258427094541152168921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8027011236126054869558561 6020258427094541152168921)
        ·
          refine ⟨4515193820320905864126691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6020258427094541152168921 4515193820320905864126691)
          ·
            refine ⟨6772790730481358796190037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4515193820320905864126691 6772790730481358796190037)
            ·
              refine ⟨19842160343207105848213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 6772790730481358796190037 19842160343207105848213)
              ·
                rfl

theorem cell20_391255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 10].length) (baseStart_391255 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391255 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391255 prefixEnd_391255 := by exact prefixLift 391255
  have htrace : WordTrace (prefixWord ++ tailWord_391255) baseStart_391255 baseEnd_391255 := by
    simpa [prefixWord, tailWord_391255, baseEnd_391255] using wordTrace_append hprefix tailTrace_391255
  have hstable : (prefixWord ++ tailWord_391255).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391255).length < 2 ^ (prefixWord ++ tailWord_391255).sum := by decide
  have hdescent : baseEnd_391255 < baseStart_391255 := by decide
  rcases family_descends (prefixWord ++ tailWord_391255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391261 : List Nat := [1, 4, 4, 1, 1, 3, 1, 1, 4]
def baseStart_391261 : Nat := 118140960795 + 391261 * 2 ^ 59
def prefixEnd_391261 : Nat := 4983230072969 + 3 ^ 40 * 391261 * 2
def baseEnd_391261 : Nat := 178582181652354598433893

theorem tailTrace_391261 : CollatzResearch.WordTrace tailWord_391261 prefixEnd_391261 178582181652354598433893 := by
  unfold tailWord_391261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14270461035535693903933637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9513640690357129269289091 14270461035535693903933637)
  ·
    refine ⟨2675711444162942606987557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14270461035535693903933637 2675711444162942606987557)
    ·
      refine ⟨501695895780551738810167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2675711444162942606987557 501695895780551738810167)
      ·
        refine ⟨752543843670827608215251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 501695895780551738810167 752543843670827608215251)
        ·
          refine ⟨1128815765506241412322877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752543843670827608215251 1128815765506241412322877)
          ·
            refine ⟨423305912064840529621079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1128815765506241412322877 423305912064840529621079)
            ·
              refine ⟨634958868097260794431619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423305912064840529621079 634958868097260794431619)
              ·
                refine ⟨952438302145891191647429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 634958868097260794431619 952438302145891191647429)
                ·
                  refine ⟨178582181652354598433893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 952438302145891191647429 178582181652354598433893)
                  ·
                    rfl

theorem cell20_391261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 1, 4].length) (baseStart_391261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391261 prefixEnd_391261 := by exact prefixLift 391261
  have htrace : WordTrace (prefixWord ++ tailWord_391261) baseStart_391261 baseEnd_391261 := by
    simpa [prefixWord, tailWord_391261, baseEnd_391261] using wordTrace_append hprefix tailTrace_391261
  have hstable : (prefixWord ++ tailWord_391261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391261).length < 2 ^ (prefixWord ++ tailWord_391261).sum := by decide
  have hdescent : baseEnd_391261 < baseStart_391261 := by decide
  rcases family_descends (prefixWord ++ tailWord_391261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391310 : List Nat := [4, 1, 1, 3, 3, 8]
def baseStart_391310 : Nat := 118140960795 + 391310 * 2 ^ 59
def prefixEnd_391310 : Nat := 4983230072969 + 3 ^ 40 * 391310 * 2
def baseEnd_391310 : Nat := 6614983206945489103717

theorem tailTrace_391310 : CollatzResearch.WordTrace tailWord_391310 prefixEnd_391310 6614983206945489103717 := by
  unfold tailWord_391310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784031026544771909058423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9514832141572116848311589 1784031026544771909058423)
  ·
    refine ⟨2676046539817157863587635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1784031026544771909058423 2676046539817157863587635)
    ·
      refine ⟨4014069809725736795381453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2676046539817157863587635 4014069809725736795381453)
      ·
        refine ⟨1505276178647151298268045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4014069809725736795381453 1505276178647151298268045)
        ·
          refine ⟨564478566992681736850517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1505276178647151298268045 564478566992681736850517)
          ·
            refine ⟨6614983206945489103717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 564478566992681736850517 6614983206945489103717)
            ·
              rfl

theorem cell20_391310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 8].length) (baseStart_391310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391310 prefixEnd_391310 := by exact prefixLift 391310
  have htrace : WordTrace (prefixWord ++ tailWord_391310) baseStart_391310 baseEnd_391310 := by
    simpa [prefixWord, tailWord_391310, baseEnd_391310] using wordTrace_append hprefix tailTrace_391310
  have hstable : (prefixWord ++ tailWord_391310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391310).length < 2 ^ (prefixWord ++ tailWord_391310).sum := by decide
  have hdescent : baseEnd_391310 < baseStart_391310 := by decide
  rcases family_descends (prefixWord ++ tailWord_391310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391316 : List Nat := [2, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_391316 : Nat := 118140960795 + 391316 * 2 ^ 59
def prefixEnd_391316 : Nat := 4983230072969 + 3 ^ 40 * 391316 * 2
def baseEnd_391316 : Nat := 178607285151018851600335

theorem tailTrace_391316 : CollatzResearch.WordTrace tailWord_391316 prefixEnd_391316 178607285151018851600335 := by
  unfold tailWord_391316
  simp only [CollatzResearch.WordTrace]
  refine ⟨7136233525168219148592901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9514978033557625531457201 7136233525168219148592901)
  ·
    refine ⟨1338043785969041090361169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7136233525168219148592901 1338043785969041090361169)
    ·
      refine ⟨1003532839476780817770877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338043785969041090361169 1003532839476780817770877)
      ·
        refine ⟨376324814803792806664079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1003532839476780817770877 376324814803792806664079)
        ·
          refine ⟨564487222205689209996119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 376324814803792806664079 564487222205689209996119)
          ·
            refine ⟨846730833308533814994179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564487222205689209996119 846730833308533814994179)
            ·
              refine ⟨1270096249962800722491269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 846730833308533814994179 1270096249962800722491269)
              ·
                refine ⟨238143046868025135467113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1270096249962800722491269 238143046868025135467113)
                ·
                  refine ⟨178607285151018851600335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238143046868025135467113 178607285151018851600335)
                  ·
                    rfl

theorem cell20_391316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_391316 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391316 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391316 prefixEnd_391316 := by exact prefixLift 391316
  have htrace : WordTrace (prefixWord ++ tailWord_391316) baseStart_391316 baseEnd_391316 := by
    simpa [prefixWord, tailWord_391316, baseEnd_391316] using wordTrace_append hprefix tailTrace_391316
  have hstable : (prefixWord ++ tailWord_391316).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391316).length < 2 ^ (prefixWord ++ tailWord_391316).sum := by decide
  have hdescent : baseEnd_391316 < baseStart_391316 := by decide
  rcases family_descends (prefixWord ++ tailWord_391316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391327 : List Nat := [1, 1, 2, 6, 1, 3, 1, 5]
def baseStart_391327 : Nat := 118140960795 + 391327 * 2 ^ 59
def prefixEnd_391327 : Nat := 4983230072969 + 3 ^ 40 * 391327 * 2
def baseEnd_391327 : Nat := 59537435283583900744541

theorem tailTrace_391327 : CollatzResearch.WordTrace tailWord_391327 prefixEnd_391327 59537435283583900744541 := by
  unfold tailWord_391327
  simp only [CollatzResearch.WordTrace]
  refine ⟨14272868253296587175836235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9515245502197724783890823 14272868253296587175836235)
  ·
    refine ⟨21409302379944880763754353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14272868253296587175836235 21409302379944880763754353)
    ·
      refine ⟨16056976784958660572815765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21409302379944880763754353 16056976784958660572815765)
      ·
        refine ⟨752670786794937214350739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16056976784958660572815765 752670786794937214350739)
        ·
          refine ⟨1129006180192405821526109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 752670786794937214350739 1129006180192405821526109)
          ·
            refine ⟨423377317572152183072291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1129006180192405821526109 423377317572152183072291)
            ·
              refine ⟨635065976358228274608437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423377317572152183072291 635065976358228274608437)
              ·
                refine ⟨59537435283583900744541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 635065976358228274608437 59537435283583900744541)
                ·
                  rfl

theorem cell20_391327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 3, 1, 5].length) (baseStart_391327 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391327 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391327 prefixEnd_391327 := by exact prefixLift 391327
  have htrace : WordTrace (prefixWord ++ tailWord_391327) baseStart_391327 baseEnd_391327 := by
    simpa [prefixWord, tailWord_391327, baseEnd_391327] using wordTrace_append hprefix tailTrace_391327
  have hstable : (prefixWord ++ tailWord_391327).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391327).length < 2 ^ (prefixWord ++ tailWord_391327).sum := by decide
  have hdescent : baseEnd_391327 < baseStart_391327 := by decide
  rcases family_descends (prefixWord ++ tailWord_391327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391341 : List Nat := [1, 5, 2, 1, 2, 1, 1, 1, 6]
def baseStart_391341 : Nat := 118140960795 + 391341 * 2 ^ 59
def prefixEnd_391341 : Nat := 4983230072969 + 3 ^ 40 * 391341 * 2
def baseEnd_391341 : Nat := 178618695832229875766899

theorem tailTrace_391341 : CollatzResearch.WordTrace tailWord_391341 prefixEnd_391341 178618695832229875766899 := by
  unfold tailWord_391341
  simp only [CollatzResearch.WordTrace]
  refine ⟨14273378875245867566845877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9515585916830578377897251 14273378875245867566845877)
  ·
    refine ⟨1338129269554300084391801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14273378875245867566845877 1338129269554300084391801)
    ·
      refine ⟨1003596952165725063293851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338129269554300084391801 1003596952165725063293851)
      ·
        refine ⟨1505395428248587594940777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1003596952165725063293851 1505395428248587594940777)
        ·
          refine ⟨1129046571186440696205583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1505395428248587594940777 1129046571186440696205583)
          ·
            refine ⟨1693569856779661044308375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1129046571186440696205583 1693569856779661044308375)
            ·
              refine ⟨2540354785169491566462563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1693569856779661044308375 2540354785169491566462563)
              ·
                refine ⟨3810532177754237349693845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2540354785169491566462563 3810532177754237349693845)
                ·
                  refine ⟨178618695832229875766899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3810532177754237349693845 178618695832229875766899)
                  ·
                    rfl

theorem cell20_391341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_391341 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391341 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391341 prefixEnd_391341 := by exact prefixLift 391341
  have htrace : WordTrace (prefixWord ++ tailWord_391341) baseStart_391341 baseEnd_391341 := by
    simpa [prefixWord, tailWord_391341, baseEnd_391341] using wordTrace_append hprefix tailTrace_391341
  have hstable : (prefixWord ++ tailWord_391341).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391341).length < 2 ^ (prefixWord ++ tailWord_391341).sum := by decide
  have hdescent : baseEnd_391341 < baseStart_391341 := by decide
  rcases family_descends (prefixWord ++ tailWord_391341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391417 : List Nat := [1, 2, 1, 3, 1, 1, 2, 7, 2]
def baseStart_391417 : Nat := 118140960795 + 391417 * 2 ^ 59
def prefixEnd_391417 : Nat := 4983230072969 + 3 ^ 40 * 391417 * 2
def baseEnd_391417 : Nat := 178653384303111389233255

theorem tailTrace_391417 : CollatzResearch.WordTrace tailWord_391417 prefixEnd_391417 178653384303111389233255 := by
  unfold tailWord_391417
  simp only [CollatzResearch.WordTrace]
  refine ⟨14276150822970532546612505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9517433881980355031075003 14276150822970532546612505)
  ·
    refine ⟨10707113117227899409959379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14276150822970532546612505 10707113117227899409959379)
    ·
      refine ⟨16060669675841849114939069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10707113117227899409959379 16060669675841849114939069)
      ·
        refine ⟨6022751128440693418102151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16060669675841849114939069 6022751128440693418102151)
        ·
          refine ⟨9034126692661040127153227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6022751128440693418102151 9034126692661040127153227)
          ·
            refine ⟨13551190038991560190729841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9034126692661040127153227 13551190038991560190729841)
            ·
              refine ⟨10163392529243670143047381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13551190038991560190729841 10163392529243670143047381)
              ·
                refine ⟨238204512404148518977673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10163392529243670143047381 238204512404148518977673)
                ·
                  refine ⟨178653384303111389233255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238204512404148518977673 178653384303111389233255)
                  ·
                    rfl

theorem cell20_391417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 7, 2].length) (baseStart_391417 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391417 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391417 prefixEnd_391417 := by exact prefixLift 391417
  have htrace : WordTrace (prefixWord ++ tailWord_391417) baseStart_391417 baseEnd_391417 := by
    simpa [prefixWord, tailWord_391417, baseEnd_391417] using wordTrace_append hprefix tailTrace_391417
  have hstable : (prefixWord ++ tailWord_391417).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391417).length < 2 ^ (prefixWord ++ tailWord_391417).sum := by decide
  have hdescent : baseEnd_391417 < baseStart_391417 := by decide
  rcases family_descends (prefixWord ++ tailWord_391417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391445 : List Nat := [1, 3, 2, 1, 2, 1, 3, 7]
def baseStart_391445 : Nat := 118140960795 + 391445 * 2 ^ 59
def prefixEnd_391445 : Nat := 4983230072969 + 3 ^ 40 * 391445 * 2
def baseEnd_391445 : Nat := 59555388088689245433269

theorem tailTrace_391445 : CollatzResearch.WordTrace tailWord_391445 prefixEnd_391445 59555388088689245433269 := by
  unfold tailWord_391445
  simp only [CollatzResearch.WordTrace]
  refine ⟨14277172066869093328631789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9518114711246062219087859 14277172066869093328631789)
  ·
    refine ⟨5353939525075909998236921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14277172066869093328631789 5353939525075909998236921)
    ·
      refine ⟨4015454643806932498677691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5353939525075909998236921 4015454643806932498677691)
      ·
        refine ⟨6023181965710398748016537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4015454643806932498677691 6023181965710398748016537)
        ·
          refine ⟨4517386474282799061012403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6023181965710398748016537 4517386474282799061012403)
          ·
            refine ⟨6776079711424198591518605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4517386474282799061012403 6776079711424198591518605)
            ·
              refine ⟨2541029891784074471819477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6776079711424198591518605 2541029891784074471819477)
              ·
                refine ⟨59555388088689245433269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2541029891784074471819477 59555388088689245433269)
                ·
                  rfl

theorem cell20_391445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 7].length) (baseStart_391445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391445 prefixEnd_391445 := by exact prefixLift 391445
  have htrace : WordTrace (prefixWord ++ tailWord_391445) baseStart_391445 baseEnd_391445 := by
    simpa [prefixWord, tailWord_391445, baseEnd_391445] using wordTrace_append hprefix tailTrace_391445
  have hstable : (prefixWord ++ tailWord_391445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391445).length < 2 ^ (prefixWord ++ tailWord_391445).sum := by decide
  have hdescent : baseEnd_391445 < baseStart_391445 := by decide
  rcases family_descends (prefixWord ++ tailWord_391445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391486 : List Nat := [4, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_391486 : Nat := 118140960795 + 391486 * 2 ^ 59
def prefixEnd_391486 : Nat := 4983230072969 + 3 ^ 40 * 391486 * 2
def baseEnd_391486 : Nat := 178684877783253815932973

theorem tailTrace_391486 : CollatzResearch.WordTrace tailWord_391486 prefixEnd_391486 178684877783253815932973 := by
  unfold tailWord_391486
  simp only [CollatzResearch.WordTrace]
  refine ⟨1784833432465069666359289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9519111639813704887249541 1784833432465069666359289)
  ·
    refine ⟨1338625074348802249769467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1784833432465069666359289 1338625074348802249769467)
    ·
      refine ⟨2007937611523203374654201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1338625074348802249769467 2007937611523203374654201)
      ·
        refine ⟨1505953208642402530990651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2007937611523203374654201 1505953208642402530990651)
        ·
          refine ⟨2258929812963603796485977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1505953208642402530990651 2258929812963603796485977)
          ·
            refine ⟨1694197359722702847364483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2258929812963603796485977 1694197359722702847364483)
            ·
              refine ⟨2541296039584054271046725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1694197359722702847364483 2541296039584054271046725)
              ·
                refine ⟨476493007422010175821261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2541296039584054271046725 476493007422010175821261)
                ·
                  refine ⟨178684877783253815932973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476493007422010175821261 178684877783253815932973)
                  ·
                    rfl

theorem cell20_391486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_391486 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391486 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391486 prefixEnd_391486 := by exact prefixLift 391486
  have htrace : WordTrace (prefixWord ++ tailWord_391486) baseStart_391486 baseEnd_391486 := by
    simpa [prefixWord, tailWord_391486, baseEnd_391486] using wordTrace_append hprefix tailTrace_391486
  have hstable : (prefixWord ++ tailWord_391486).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391486).length < 2 ^ (prefixWord ++ tailWord_391486).sum := by decide
  have hdescent : baseEnd_391486 < baseStart_391486 := by decide
  rcases family_descends (prefixWord ++ tailWord_391486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391489 : List Nat := [1, 2, 5, 2, 2, 1, 1, 4, 2]
def baseStart_391489 : Nat := 118140960795 + 391489 * 2 ^ 59
def prefixEnd_391489 : Nat := 4983230072969 + 3 ^ 40 * 391489 * 2
def baseEnd_391489 : Nat := 178686247064999138832961

theorem tailTrace_391489 : CollatzResearch.WordTrace tailWord_391489 prefixEnd_391489 178686247064999138832961 := by
  unfold tailWord_391489
  simp only [CollatzResearch.WordTrace]
  refine ⟨14278776878709688843233521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9519184585806459228822347 14278776878709688843233521)
  ·
    refine ⟨10709082659032266632425141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14278776878709688843233521 10709082659032266632425141)
    ·
      refine ⟨1003976499284274996789857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10709082659032266632425141 1003976499284274996789857)
      ·
        refine ⟨752982374463206247592393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1003976499284274996789857 752982374463206247592393)
        ·
          refine ⟨564736780847404685694295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 752982374463206247592393 564736780847404685694295)
          ·
            refine ⟨847105171271107028541443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 564736780847404685694295 847105171271107028541443)
            ·
              refine ⟨1270657756906660542812165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847105171271107028541443 1270657756906660542812165)
              ·
                refine ⟨238248329419998851777281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1270657756906660542812165 238248329419998851777281)
                ·
                  refine ⟨178686247064999138832961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238248329419998851777281 178686247064999138832961)
                  ·
                    rfl

theorem cell20_391489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 4, 2].length) (baseStart_391489 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391489 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391489 prefixEnd_391489 := by exact prefixLift 391489
  have htrace : WordTrace (prefixWord ++ tailWord_391489) baseStart_391489 baseEnd_391489 := by
    simpa [prefixWord, tailWord_391489, baseEnd_391489] using wordTrace_append hprefix tailTrace_391489
  have hstable : (prefixWord ++ tailWord_391489).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391489).length < 2 ^ (prefixWord ++ tailWord_391489).sum := by decide
  have hdescent : baseEnd_391489 < baseStart_391489 := by decide
  rcases family_descends (prefixWord ++ tailWord_391489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391541 : List Nat := [1, 3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_391541 : Nat := 118140960795 + 391541 * 2 ^ 59
def prefixEnd_391541 : Nat := 4983230072969 + 3 ^ 40 * 391541 * 2
def baseEnd_391541 : Nat := 178709981281918069099415

theorem tailTrace_391541 : CollatzResearch.WordTrace tailWord_391541 prefixEnd_391541 178709981281918069099415 := by
  unfold tailWord_391541
  simp only [CollatzResearch.WordTrace]
  refine ⟨14280673474521301724126477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9520448983014201149417651 14280673474521301724126477)
  ·
    refine ⟨5355252552945488146547429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14280673474521301724126477 5355252552945488146547429)
    ·
      refine ⟨1004109853677279027477643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5355252552945488146547429 1004109853677279027477643)
      ·
        refine ⟨1506164780515918541216465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004109853677279027477643 1506164780515918541216465)
        ·
          refine ⟨1129623585386938905912349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1506164780515918541216465 1129623585386938905912349)
          ·
            refine ⟨423608844520102089717131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1129623585386938905912349 423608844520102089717131)
            ·
              refine ⟨635413266780153134575697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423608844520102089717131 635413266780153134575697)
              ·
                refine ⟨476559950085114850931773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635413266780153134575697 476559950085114850931773)
                ·
                  refine ⟨178709981281918069099415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476559950085114850931773 178709981281918069099415)
                  ·
                    rfl

theorem cell20_391541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_391541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391541 prefixEnd_391541 := by exact prefixLift 391541
  have htrace : WordTrace (prefixWord ++ tailWord_391541) baseStart_391541 baseEnd_391541 := by
    simpa [prefixWord, tailWord_391541, baseEnd_391541] using wordTrace_append hprefix tailTrace_391541
  have hstable : (prefixWord ++ tailWord_391541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391541).length < 2 ^ (prefixWord ++ tailWord_391541).sum := by decide
  have hdescent : baseEnd_391541 < baseStart_391541 := by decide
  rcases family_descends (prefixWord ++ tailWord_391541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391559 : List Nat := [1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_391559 : Nat := 118140960795 + 391559 * 2 ^ 59
def prefixEnd_391559 : Nat := 4983230072969 + 3 ^ 40 * 391559 * 2
def baseEnd_391559 : Nat := 59572732324130002166447

theorem tailTrace_391559 : CollatzResearch.WordTrace tailWord_391559 prefixEnd_391559 59572732324130002166447 := by
  unfold tailWord_391559
  simp only [CollatzResearch.WordTrace]
  refine ⟨14281329988456090798281731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9520886658970727198854487 14281329988456090798281731)
  ·
    refine ⟨21421994982684136197422597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14281329988456090798281731 21421994982684136197422597)
    ·
      refine ⟨4016624059253275537016737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21421994982684136197422597 4016624059253275537016737)
      ·
        refine ⟨3012468044439956652762553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4016624059253275537016737 3012468044439956652762553)
        ·
          refine ⟨2259351033329967489571915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3012468044439956652762553 2259351033329967489571915)
          ·
            refine ⟨3389026549994951234357873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2259351033329967489571915 3389026549994951234357873)
            ·
              refine ⟨2541769912496213425768405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3389026549994951234357873 2541769912496213425768405)
              ·
                refine ⟨59572732324130002166447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2541769912496213425768405 59572732324130002166447)
                ·
                  rfl

theorem cell20_391559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_391559 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391559 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391559 prefixEnd_391559 := by exact prefixLift 391559
  have htrace : WordTrace (prefixWord ++ tailWord_391559) baseStart_391559 baseEnd_391559 := by
    simpa [prefixWord, tailWord_391559, baseEnd_391559] using wordTrace_append hprefix tailTrace_391559
  have hstable : (prefixWord ++ tailWord_391559).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391559).length < 2 ^ (prefixWord ++ tailWord_391559).sum := by decide
  have hdescent : baseEnd_391559 < baseStart_391559 := by decide
  rcases family_descends (prefixWord ++ tailWord_391559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391572 : List Nat := [2, 4, 2, 1, 3, 2, 2, 4]
def baseStart_391572 : Nat := 118140960795 + 391572 * 2 ^ 59
def prefixEnd_391572 : Nat := 4983230072969 + 3 ^ 40 * 391572 * 2
def baseEnd_391572 : Nat := 59574710175539913021985

theorem tailTrace_391572 : CollatzResearch.WordTrace tailWord_391572 prefixEnd_391572 59574710175539913021985 := by
  unfold tailWord_391572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140902068704497009252485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9521202758272662679003313 7140902068704497009252485)
  ·
    refine ⟨1338919137882093189234841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7140902068704497009252485 1338919137882093189234841)
    ·
      refine ⟨1004189353411569891926131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1338919137882093189234841 1004189353411569891926131)
      ·
        refine ⟨1506284030117354837889197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004189353411569891926131 1506284030117354837889197)
        ·
          refine ⟨564856511294008064208449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1506284030117354837889197 564856511294008064208449)
          ·
            refine ⟨423642383470506048156337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 564856511294008064208449 423642383470506048156337)
            ·
              refine ⟨317731787602879536117253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423642383470506048156337 317731787602879536117253)
              ·
                refine ⟨59574710175539913021985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317731787602879536117253 59574710175539913021985)
                ·
                  rfl

theorem cell20_391572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 2, 2, 4].length) (baseStart_391572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391572 prefixEnd_391572 := by exact prefixLift 391572
  have htrace : WordTrace (prefixWord ++ tailWord_391572) baseStart_391572 baseEnd_391572 := by
    simpa [prefixWord, tailWord_391572, baseEnd_391572] using wordTrace_append hprefix tailTrace_391572
  have hstable : (prefixWord ++ tailWord_391572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391572).length < 2 ^ (prefixWord ++ tailWord_391572).sum := by decide
  have hdescent : baseEnd_391572 < baseStart_391572 := by decide
  rcases family_descends (prefixWord ++ tailWord_391572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391576 : List Nat := [2, 1, 2, 5, 1, 2, 1, 6]
def baseStart_391576 : Nat := 118140960795 + 391576 * 2 ^ 59
def prefixEnd_391576 : Nat := 4983230072969 + 3 ^ 40 * 391576 * 2
def baseEnd_391576 : Nat := 59575318745204500977535

theorem tailTrace_391576 : CollatzResearch.WordTrace tailWord_391576 prefixEnd_391576 59575318745204500977535 := by
  unfold tailWord_391576
  simp only [CollatzResearch.WordTrace]
  refine ⟨7140975014697251350825291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9521300019596335134433721 7140975014697251350825291)
  ·
    refine ⟨10711462522045877026237937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7140975014697251350825291 10711462522045877026237937)
    ·
      refine ⟨8033596891534407769678453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10711462522045877026237937 8033596891534407769678453)
      ·
        refine ⟨753149708581350728407355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8033596891534407769678453 753149708581350728407355)
        ·
          refine ⟨1129724562872026092611033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753149708581350728407355 1129724562872026092611033)
          ·
            refine ⟨847293422154019569458275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1129724562872026092611033 847293422154019569458275)
            ·
              refine ⟨1270940133231029354187413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847293422154019569458275 1270940133231029354187413)
              ·
                refine ⟨59575318745204500977535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1270940133231029354187413 59575318745204500977535)
                ·
                  rfl

theorem cell20_391576_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_391576 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391576 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391576 prefixEnd_391576 := by exact prefixLift 391576
  have htrace : WordTrace (prefixWord ++ tailWord_391576) baseStart_391576 baseEnd_391576 := by
    simpa [prefixWord, tailWord_391576, baseEnd_391576] using wordTrace_append hprefix tailTrace_391576
  have hstable : (prefixWord ++ tailWord_391576).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391576).length < 2 ^ (prefixWord ++ tailWord_391576).sum := by decide
  have hdescent : baseEnd_391576 < baseStart_391576 := by decide
  rcases family_descends (prefixWord ++ tailWord_391576) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391582 : List Nat := [4, 3, 1, 2, 1, 3, 1, 3, 2]
def baseStart_391582 : Nat := 118140960795 + 391582 * 2 ^ 59
def prefixEnd_391582 : Nat := 4983230072969 + 3 ^ 40 * 391582 * 2
def baseEnd_391582 : Nat := 178728694799104148732581

theorem tailTrace_391582 : CollatzResearch.WordTrace tailWord_391582 prefixEnd_391582 178728694799104148732581 := by
  unfold tailWord_391582
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785271108421595715796125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9521445911581843817579333 1785271108421595715796125)
  ·
    refine ⟨669476665658098393423547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1785271108421595715796125 669476665658098393423547)
    ·
      refine ⟨1004214998487147590135321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 669476665658098393423547 1004214998487147590135321)
      ·
        refine ⟨753161248865360692601491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004214998487147590135321 753161248865360692601491)
        ·
          refine ⟨1129741873298041038902237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753161248865360692601491 1129741873298041038902237)
          ·
            refine ⟨423653202486765389588339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1129741873298041038902237 423653202486765389588339)
            ·
              refine ⟨635479803730148084382509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423653202486765389588339 635479803730148084382509)
              ·
                refine ⟨238304926398805531643441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635479803730148084382509 238304926398805531643441)
                ·
                  refine ⟨178728694799104148732581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238304926398805531643441 178728694799104148732581)
                  ·
                    rfl

theorem cell20_391582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_391582 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391582 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391582 prefixEnd_391582 := by exact prefixLift 391582
  have htrace : WordTrace (prefixWord ++ tailWord_391582) baseStart_391582 baseEnd_391582 := by
    simpa [prefixWord, tailWord_391582, baseEnd_391582] using wordTrace_append hprefix tailTrace_391582
  have hstable : (prefixWord ++ tailWord_391582).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391582).length < 2 ^ (prefixWord ++ tailWord_391582).sum := by decide
  have hdescent : baseEnd_391582 < baseStart_391582 := by decide
  rcases family_descends (prefixWord ++ tailWord_391582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391607 : List Nat := [1, 1, 3, 1, 3, 5, 1, 1, 4]
def baseStart_391607 : Nat := 118140960795 + 391607 * 2 ^ 59
def prefixEnd_391607 : Nat := 4983230072969 + 3 ^ 40 * 391607 * 2
def baseEnd_391607 : Nat := 178740105480315172899145

theorem tailTrace_391607 : CollatzResearch.WordTrace tailWord_391607 prefixEnd_391607 178740105480315172899145 := by
  unfold tailWord_391607
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283080692282194996029075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9522053794854796664019383 14283080692282194996029075)
  ·
    refine ⟨21424621038423292494043613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14283080692282194996029075 21424621038423292494043613)
    ·
      refine ⟨8034232889408734685266355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21424621038423292494043613 8034232889408734685266355)
      ·
        refine ⟨12051349334113102027899533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8034232889408734685266355 12051349334113102027899533)
        ·
          refine ⟨4519256000292413260462325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12051349334113102027899533 4519256000292413260462325)
          ·
            refine ⟨423680250027413743168343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4519256000292413260462325 423680250027413743168343)
            ·
              refine ⟨635520375041120614752515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 423680250027413743168343 635520375041120614752515)
              ·
                refine ⟨953280562561680922128773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 635520375041120614752515 953280562561680922128773)
                ·
                  refine ⟨178740105480315172899145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 953280562561680922128773 178740105480315172899145)
                  ·
                    rfl

theorem cell20_391607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 1, 1, 4].length) (baseStart_391607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391607 prefixEnd_391607 := by exact prefixLift 391607
  have htrace : WordTrace (prefixWord ++ tailWord_391607) baseStart_391607 baseEnd_391607 := by
    simpa [prefixWord, tailWord_391607, baseEnd_391607] using wordTrace_append hprefix tailTrace_391607
  have hstable : (prefixWord ++ tailWord_391607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391607).length < 2 ^ (prefixWord ++ tailWord_391607).sum := by decide
  have hdescent : baseEnd_391607 < baseStart_391607 := by decide
  rcases family_descends (prefixWord ++ tailWord_391607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391611 : List Nat := [1, 1, 1, 1, 1, 2, 2, 1, 10]
def baseStart_391611 : Nat := 118140960795 + 391611 * 2 ^ 59
def prefixEnd_391611 : Nat := 4983230072969 + 3 ^ 40 * 391611 * 2
def baseEnd_391611 : Nat := 178741931189308936765795

theorem tailTrace_391611 : CollatzResearch.WordTrace tailWord_391611 prefixEnd_391611 178741931189308936765795 := by
  unfold tailWord_391611
  simp only [CollatzResearch.WordTrace]
  refine ⟨14283226584267703679174687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9522151056178469119449791 14283226584267703679174687)
  ·
    refine ⟨21424839876401555518762031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14283226584267703679174687 21424839876401555518762031)
    ·
      refine ⟨32137259814602333278143047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21424839876401555518762031 32137259814602333278143047)
      ·
        refine ⟨48205889721903499917214571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32137259814602333278143047 48205889721903499917214571)
        ·
          refine ⟨72308834582855249875821857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48205889721903499917214571 72308834582855249875821857)
          ·
            refine ⟨54231625937141437406866393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 72308834582855249875821857 54231625937141437406866393)
            ·
              refine ⟨40673719452856078055149795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 54231625937141437406866393 40673719452856078055149795)
              ·
                refine ⟨61010579179284117082724693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 40673719452856078055149795 61010579179284117082724693)
                ·
                  refine ⟨178741931189308936765795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 61010579179284117082724693 178741931189308936765795)
                  ·
                    rfl

theorem cell20_391611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 1, 10].length) (baseStart_391611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391611 prefixEnd_391611 := by exact prefixLift 391611
  have htrace : WordTrace (prefixWord ++ tailWord_391611) baseStart_391611 baseEnd_391611 := by
    simpa [prefixWord, tailWord_391611, baseEnd_391611] using wordTrace_append hprefix tailTrace_391611
  have hstable : (prefixWord ++ tailWord_391611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391611).length < 2 ^ (prefixWord ++ tailWord_391611).sum := by decide
  have hdescent : baseEnd_391611 < baseStart_391611 := by decide
  rcases family_descends (prefixWord ++ tailWord_391611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391659 : List Nat := [1, 1, 1, 1, 2, 3, 6, 2, 3]
def baseStart_391659 : Nat := 118140960795 + 391659 * 2 ^ 59
def prefixEnd_391659 : Nat := 4983230072969 + 3 ^ 40 * 391659 * 2
def baseEnd_391659 : Nat := 178763839697234103165599

theorem tailTrace_391659 : CollatzResearch.WordTrace tailWord_391659 prefixEnd_391659 178763839697234103165599 := by
  unfold tailWord_391659
  simp only [CollatzResearch.WordTrace]
  refine ⟨14284977288093807876922031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9523318192062538584614687 14284977288093807876922031)
  ·
    refine ⟨21427465932140711815383047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14284977288093807876922031 21427465932140711815383047)
    ·
      refine ⟨32141198898211067723074571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21427465932140711815383047 32141198898211067723074571)
      ·
        refine ⟨48211798347316601584611857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32141198898211067723074571 48211798347316601584611857)
        ·
          refine ⟨36158848760487451188458893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48211798347316601584611857 36158848760487451188458893)
          ·
            refine ⟨13559568285182794195672085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36158848760487451188458893 13559568285182794195672085)
            ·
              refine ⟨635604763367943477922129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 13559568285182794195672085 635604763367943477922129)
              ·
                refine ⟨476703572525957608441597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 635604763367943477922129 476703572525957608441597)
                ·
                  refine ⟨178763839697234103165599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476703572525957608441597 178763839697234103165599)
                  ·
                    rfl

theorem cell20_391659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 6, 2, 3].length) (baseStart_391659 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391659 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391659 prefixEnd_391659 := by exact prefixLift 391659
  have htrace : WordTrace (prefixWord ++ tailWord_391659) baseStart_391659 baseEnd_391659 := by
    simpa [prefixWord, tailWord_391659, baseEnd_391659] using wordTrace_append hprefix tailTrace_391659
  have hstable : (prefixWord ++ tailWord_391659).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391659).length < 2 ^ (prefixWord ++ tailWord_391659).sum := by decide
  have hdescent : baseEnd_391659 < baseStart_391659 := by decide
  rcases family_descends (prefixWord ++ tailWord_391659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391662 : List Nat := [4, 1, 2, 1, 2, 3, 1, 4, 2]
def baseStart_391662 : Nat := 118140960795 + 391662 * 2 ^ 59
def prefixEnd_391662 : Nat := 4983230072969 + 3 ^ 40 * 391662 * 2
def baseEnd_391662 : Nat := 178765208978979426065587

theorem tailTrace_391662 : CollatzResearch.WordTrace tailWord_391662 prefixEnd_391662 178765208978979426065587 := by
  unfold tailWord_391662
  simp only [CollatzResearch.WordTrace]
  refine ⟨1785635838385367423660155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9523391138055292926187493 1785635838385367423660155)
  ·
    refine ⟨2678453757578051135490233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1785635838385367423660155 2678453757578051135490233)
    ·
      refine ⟨2008840318183538351617675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2678453757578051135490233 2008840318183538351617675)
      ·
        refine ⟨3013260477275307527426513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2008840318183538351617675 3013260477275307527426513)
        ·
          refine ⟨2259945357956480645569885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013260477275307527426513 2259945357956480645569885)
          ·
            refine ⟨847479509233680242088707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2259945357956480645569885 847479509233680242088707)
            ·
              refine ⟨1271219263850520363133061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847479509233680242088707 1271219263850520363133061)
              ·
                refine ⟨238353611971972568087449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1271219263850520363133061 238353611971972568087449)
                ·
                  refine ⟨178765208978979426065587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238353611971972568087449 178765208978979426065587)
                  ·
                    rfl

theorem cell20_391662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 4, 2].length) (baseStart_391662 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391662 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391662 prefixEnd_391662 := by exact prefixLift 391662
  have htrace : WordTrace (prefixWord ++ tailWord_391662) baseStart_391662 baseEnd_391662 := by
    simpa [prefixWord, tailWord_391662, baseEnd_391662] using wordTrace_append hprefix tailTrace_391662
  have hstable : (prefixWord ++ tailWord_391662).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391662).length < 2 ^ (prefixWord ++ tailWord_391662).sum := by decide
  have hdescent : baseEnd_391662 < baseStart_391662 := by decide
  rcases family_descends (prefixWord ++ tailWord_391662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391673 : List Nat := [1, 2, 1, 3, 1, 2, 5, 5]
def baseStart_391673 : Nat := 118140960795 + 391673 * 2 ^ 59
def prefixEnd_391673 : Nat := 4983230072969 + 3 ^ 40 * 391673 * 2
def baseEnd_391673 : Nat := 59590076559570758899625

theorem tailTrace_391673 : CollatzResearch.WordTrace tailWord_391673 prefixEnd_391673 59590076559570758899625 := by
  unfold tailWord_391673
  simp only [CollatzResearch.WordTrace]
  refine ⟨14285487910043088267931673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9523658606695392178621115 14285487910043088267931673)
  ·
    refine ⟨10714115932532316200948755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14285487910043088267931673 10714115932532316200948755)
    ·
      refine ⟨16071173898798474301423133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10714115932532316200948755 16071173898798474301423133)
      ·
        refine ⟨6026690212049427863033675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16071173898798474301423133 6026690212049427863033675)
        ·
          refine ⟨9040035318074141794550513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6026690212049427863033675 9040035318074141794550513)
          ·
            refine ⟨6780026488555606345912885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9040035318074141794550513 6780026488555606345912885)
            ·
              refine ⟨635627483302088094929333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6780026488555606345912885 635627483302088094929333)
              ·
                refine ⟨59590076559570758899625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 635627483302088094929333 59590076559570758899625)
                ·
                  rfl

theorem cell20_391673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 5, 5].length) (baseStart_391673 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391673 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391673 prefixEnd_391673 := by exact prefixLift 391673
  have htrace : WordTrace (prefixWord ++ tailWord_391673) baseStart_391673 baseEnd_391673 := by
    simpa [prefixWord, tailWord_391673, baseEnd_391673] using wordTrace_append hprefix tailTrace_391673
  have hstable : (prefixWord ++ tailWord_391673).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391673).length < 2 ^ (prefixWord ++ tailWord_391673).sum := by decide
  have hdescent : baseEnd_391673 < baseStart_391673 := by decide
  rcases family_descends (prefixWord ++ tailWord_391673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391690 : List Nat := [3, 1, 2, 2, 2, 1, 5, 4]
def baseStart_391690 : Nat := 118140960795 + 391690 * 2 ^ 59
def prefixEnd_391690 : Nat := 4983230072969 + 3 ^ 40 * 391690 * 2
def baseEnd_391690 : Nat := 59592662980645257710713

theorem tailTrace_391690 : CollatzResearch.WordTrace tailWord_391690 prefixEnd_391690 59592662980645257710713 := by
  unfold tailWord_391690
  simp only [CollatzResearch.WordTrace]
  refine ⟨3571526987745375042825131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9524071967321000114200349 3571526987745375042825131)
  ·
    refine ⟨5357290481618062564237697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3571526987745375042825131 5357290481618062564237697)
    ·
      refine ⟨4017967861213546923178273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5357290481618062564237697 4017967861213546923178273)
      ·
        refine ⟨3013475895910160192383705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4017967861213546923178273 3013475895910160192383705)
        ·
          refine ⟨2260106921932620144287779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3013475895910160192383705 2260106921932620144287779)
          ·
            refine ⟨3390160382898930216431669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2260106921932620144287779 3390160382898930216431669)
            ·
              refine ⟨317827535896774707790469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3390160382898930216431669 317827535896774707790469)
              ·
                refine ⟨59592662980645257710713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317827535896774707790469 59592662980645257710713)
                ·
                  rfl

theorem cell20_391690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_391690 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391690 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391690 prefixEnd_391690 := by exact prefixLift 391690
  have htrace : WordTrace (prefixWord ++ tailWord_391690) baseStart_391690 baseEnd_391690 := by
    simpa [prefixWord, tailWord_391690, baseEnd_391690] using wordTrace_append hprefix tailTrace_391690
  have hstable : (prefixWord ++ tailWord_391690).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391690).length < 2 ^ (prefixWord ++ tailWord_391690).sum := by decide
  have hdescent : baseEnd_391690 < baseStart_391690 := by decide
  rcases family_descends (prefixWord ++ tailWord_391690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391745 : List Nat := [1, 2, 5, 1, 1, 4, 2, 4]
def baseStart_391745 : Nat := 118140960795 + 391745 * 2 ^ 59
def prefixEnd_391745 : Nat := 4983230072969 + 3 ^ 40 * 391745 * 2
def baseEnd_391745 : Nat := 59601030813533342099527

theorem tailTrace_391745 : CollatzResearch.WordTrace tailWord_391745 prefixEnd_391745 59601030813533342099527 := by
  unfold tailWord_391745
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288113965782244564552689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9525409310521496376368459 14288113965782244564552689)
  ·
    refine ⟨10716085474336683423414517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14288113965782244564552689 10716085474336683423414517)
    ·
      refine ⟨1004633013219064070945111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10716085474336683423414517 1004633013219064070945111)
      ·
        refine ⟨1506949519828596106417667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1004633013219064070945111 1506949519828596106417667)
        ·
          refine ⟨2260424279742894159626501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1506949519828596106417667 2260424279742894159626501)
          ·
            refine ⟨423829552451792654929969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2260424279742894159626501 423829552451792654929969)
            ·
              refine ⟨317872164338844491197477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 423829552451792654929969 317872164338844491197477)
              ·
                refine ⟨59601030813533342099527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 317872164338844491197477 59601030813533342099527)
                ·
                  rfl

theorem cell20_391745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 4, 2, 4].length) (baseStart_391745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391745 prefixEnd_391745 := by exact prefixLift 391745
  have htrace : WordTrace (prefixWord ++ tailWord_391745) baseStart_391745 baseEnd_391745 := by
    simpa [prefixWord, tailWord_391745, baseEnd_391745] using wordTrace_append hprefix tailTrace_391745
  have hstable : (prefixWord ++ tailWord_391745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391745).length < 2 ^ (prefixWord ++ tailWord_391745).sum := by decide
  have hdescent : baseEnd_391745 < baseStart_391745 := by decide
  rcases family_descends (prefixWord ++ tailWord_391745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391749 : List Nat := [1, 3, 1, 1, 1, 6, 1, 6]
def baseStart_391749 : Nat := 118140960795 + 391749 * 2 ^ 59
def prefixEnd_391749 : Nat := 4983230072969 + 3 ^ 40 * 391749 * 2
def baseEnd_391749 : Nat := 59601639383197930055077

theorem tailTrace_391749 : CollatzResearch.WordTrace tailWord_391749 prefixEnd_391749 59601639383197930055077 := by
  unfold tailWord_391749
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288259857767753247698301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9525506571845168831798867 14288259857767753247698301)
  ·
    refine ⟨5358097446662907467886863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14288259857767753247698301 5358097446662907467886863)
    ·
      refine ⟨8037146169994361201830295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358097446662907467886863 8037146169994361201830295)
      ·
        refine ⟨12055719254991541802745443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8037146169994361201830295 12055719254991541802745443)
        ·
          refine ⟨18083578882487312704118165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12055719254991541802745443 18083578882487312704118165)
          ·
            refine ⟨847667760116592783005539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18083578882487312704118165 847667760116592783005539)
            ·
              refine ⟨1271501640174889174508309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847667760116592783005539 1271501640174889174508309)
              ·
                refine ⟨59601639383197930055077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1271501640174889174508309 59601639383197930055077)
                ·
                  rfl

theorem cell20_391749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 6, 1, 6].length) (baseStart_391749 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391749 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391749 prefixEnd_391749 := by exact prefixLift 391749
  have htrace : WordTrace (prefixWord ++ tailWord_391749) baseStart_391749 baseEnd_391749 := by
    simpa [prefixWord, tailWord_391749, baseEnd_391749] using wordTrace_append hprefix tailTrace_391749
  have hstable : (prefixWord ++ tailWord_391749).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391749).length < 2 ^ (prefixWord ++ tailWord_391749).sum := by decide
  have hdescent : baseEnd_391749 < baseStart_391749 := by decide
  rcases family_descends (prefixWord ++ tailWord_391749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391756 : List Nat := [2, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_391756 : Nat := 118140960795 + 391756 * 2 ^ 59
def prefixEnd_391756 : Nat := 4983230072969 + 3 ^ 40 * 391756 * 2
def baseEnd_391756 : Nat := 178808113140332876931869

theorem tailTrace_391756 : CollatzResearch.WordTrace tailWord_391756 prefixEnd_391756 178808113140332876931869 := by
  unfold tailWord_391756
  simp only [CollatzResearch.WordTrace]
  refine ⟨7144257584371196721601561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9525676779161595628802081 7144257584371196721601561)
  ·
    refine ⟨5358193188278397541201171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7144257584371196721601561 5358193188278397541201171)
    ·
      refine ⟨8037289782417596311801757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5358193188278397541201171 8037289782417596311801757)
      ·
        refine ⟨3013983668406598616925659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8037289782417596311801757 3013983668406598616925659)
        ·
          refine ⟨4520975502609897925388489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3013983668406598616925659 4520975502609897925388489)
          ·
            refine ⟨3390731626957423444041367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4520975502609897925388489 3390731626957423444041367)
            ·
              refine ⟨5086097440436135166062051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3390731626957423444041367 5086097440436135166062051)
              ·
                refine ⟨7629146160654202749093077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5086097440436135166062051 7629146160654202749093077)
                ·
                  refine ⟨178808113140332876931869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7629146160654202749093077 178808113140332876931869)
                  ·
                    rfl

theorem cell20_391756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_391756 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391756 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391756 prefixEnd_391756 := by exact prefixLift 391756
  have htrace : WordTrace (prefixWord ++ tailWord_391756) baseStart_391756 baseEnd_391756 := by
    simpa [prefixWord, tailWord_391756, baseEnd_391756] using wordTrace_append hprefix tailTrace_391756
  have hstable : (prefixWord ++ tailWord_391756).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391756).length < 2 ^ (prefixWord ++ tailWord_391756).sum := by decide
  have hdescent : baseEnd_391756 < baseStart_391756 := by decide
  rcases family_descends (prefixWord ++ tailWord_391756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391759 : List Nat := [1, 1, 2, 1, 1, 2, 7, 3, 2]
def baseStart_391759 : Nat := 118140960795 + 391759 * 2 ^ 59
def prefixEnd_391759 : Nat := 4983230072969 + 3 ^ 40 * 391759 * 2
def baseEnd_391759 : Nat := 178809482422078199831857

theorem tailTrace_391759 : CollatzResearch.WordTrace tailWord_391759 prefixEnd_391759 178809482422078199831857 := by
  unfold tailWord_391759
  simp only [CollatzResearch.WordTrace]
  refine ⟨14288624587731524955562331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9525749725154349970374887 14288624587731524955562331)
  ·
    refine ⟨21432936881597287433343497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14288624587731524955562331 21432936881597287433343497)
    ·
      refine ⟨16074702661197965575007623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21432936881597287433343497 16074702661197965575007623)
      ·
        refine ⟨24112053991796948362511435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16074702661197965575007623 24112053991796948362511435)
        ·
          refine ⟨36168080987695422543767153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24112053991796948362511435 36168080987695422543767153)
          ·
            refine ⟨27126060740771566907825365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 36168080987695422543767153 27126060740771566907825365)
            ·
              refine ⟨635767048611833599402157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 27126060740771566907825365 635767048611833599402157)
              ·
                refine ⟨238412643229437599775809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 635767048611833599402157 238412643229437599775809)
                ·
                  refine ⟨178809482422078199831857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238412643229437599775809 178809482422078199831857)
                  ·
                    rfl

theorem cell20_391759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 7, 3, 2].length) (baseStart_391759 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391759 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391759 prefixEnd_391759 := by exact prefixLift 391759
  have htrace : WordTrace (prefixWord ++ tailWord_391759) baseStart_391759 baseEnd_391759 := by
    simpa [prefixWord, tailWord_391759, baseEnd_391759] using wordTrace_append hprefix tailTrace_391759
  have hstable : (prefixWord ++ tailWord_391759).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391759).length < 2 ^ (prefixWord ++ tailWord_391759).sum := by decide
  have hdescent : baseEnd_391759 < baseStart_391759 := by decide
  rcases family_descends (prefixWord ++ tailWord_391759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391790 : List Nat := [4, 1, 2, 2, 2, 2, 1, 3, 3]
def baseStart_391790 : Nat := 118140960795 + 391790 * 2 ^ 59
def prefixEnd_391790 : Nat := 4983230072969 + 3 ^ 40 * 391790 * 2
def baseEnd_391790 : Nat := 178823631666779869798397

theorem tailTrace_391790 : CollatzResearch.WordTrace tailWord_391790 prefixEnd_391790 178823631666779869798397 := by
  unfold tailWord_391790
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786219406327402156242603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9526503500412811499960549 1786219406327402156242603)
  ·
    refine ⟨2679329109491103234363905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786219406327402156242603 2679329109491103234363905)
    ·
      refine ⟨2009496832118327425772929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2679329109491103234363905 2009496832118327425772929)
      ·
        refine ⟨1507122624088745569329697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2009496832118327425772929 1507122624088745569329697)
        ·
          refine ⟨1130341968066559176997273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1507122624088745569329697 1130341968066559176997273)
          ·
            refine ⟨847756476049919382747955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1130341968066559176997273 847756476049919382747955)
            ·
              refine ⟨1271634714074879074121933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 847756476049919382747955 1271634714074879074121933)
              ·
                refine ⟨476863017778079652795725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1271634714074879074121933 476863017778079652795725)
                ·
                  refine ⟨178823631666779869798397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476863017778079652795725 178823631666779869798397)
                  ·
                    rfl

theorem cell20_391790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 2, 1, 3, 3].length) (baseStart_391790 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391790 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391790 prefixEnd_391790 := by exact prefixLift 391790
  have htrace : WordTrace (prefixWord ++ tailWord_391790) baseStart_391790 baseEnd_391790 := by
    simpa [prefixWord, tailWord_391790, baseEnd_391790] using wordTrace_append hprefix tailTrace_391790
  have hstable : (prefixWord ++ tailWord_391790).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391790).length < 2 ^ (prefixWord ++ tailWord_391790).sum := by decide
  have hdescent : baseEnd_391790 < baseStart_391790 := by decide
  rcases family_descends (prefixWord ++ tailWord_391790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391828 : List Nat := [2, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_391828 : Nat := 118140960795 + 391828 * 2 ^ 59
def prefixEnd_391828 : Nat := 4983230072969 + 3 ^ 40 * 391828 * 2
def baseEnd_391828 : Nat := 178840975902220626531575

theorem tailTrace_391828 : CollatzResearch.WordTrace tailWord_391828 prefixEnd_391828 178840975902220626531575 := by
  unfold tailWord_391828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7145570612240774869912069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9527427482987699826549425 7145570612240774869912069)
  ·
    refine ⟨1339794489795145288108513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7145570612240774869912069 1339794489795145288108513)
    ·
      refine ⟨1004845867346358966081385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1339794489795145288108513 1004845867346358966081385)
      ·
        refine ⟨753634400509769224561039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1004845867346358966081385 753634400509769224561039)
        ·
          refine ⟨1130451600764653836841559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 753634400509769224561039 1130451600764653836841559)
          ·
            refine ⟨1695677401146980755262339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1130451600764653836841559 1695677401146980755262339)
            ·
              refine ⟨2543516101720471132893509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1695677401146980755262339 2543516101720471132893509)
              ·
                refine ⟨476909269072588337417533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2543516101720471132893509 476909269072588337417533)
                ·
                  refine ⟨178840975902220626531575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 476909269072588337417533 178840975902220626531575)
                  ·
                    rfl

theorem cell20_391828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_391828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391828 prefixEnd_391828 := by exact prefixLift 391828
  have htrace : WordTrace (prefixWord ++ tailWord_391828) baseStart_391828 baseEnd_391828 := by
    simpa [prefixWord, tailWord_391828, baseEnd_391828] using wordTrace_append hprefix tailTrace_391828
  have hstable : (prefixWord ++ tailWord_391828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391828).length < 2 ^ (prefixWord ++ tailWord_391828).sum := by decide
  have hdescent : baseEnd_391828 < baseStart_391828 := by decide
  rcases family_descends (prefixWord ++ tailWord_391828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391918 : List Nat := [4, 1, 2, 1, 1, 3, 4, 4]
def baseStart_391918 : Nat := 118140960795 + 391918 * 2 ^ 59
def prefixEnd_391918 : Nat := 4983230072969 + 3 ^ 40 * 391918 * 2
def baseEnd_391918 : Nat := 59627351451526771177069

theorem tailTrace_391918 : CollatzResearch.WordTrace tailWord_391918 prefixEnd_391918 59627351451526771177069 := by
  unfold tailWord_391918
  simp only [CollatzResearch.WordTrace]
  refine ⟨1786802974269436888825051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9529615862770330073733605 1786802974269436888825051)
  ·
    refine ⟨2680204461404155333237577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1786802974269436888825051 2680204461404155333237577)
    ·
      refine ⟨2010153346053116499928183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2680204461404155333237577 2010153346053116499928183)
      ·
        refine ⟨3015230019079674749892275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2010153346053116499928183 3015230019079674749892275)
        ·
          refine ⟨4522845028619512124838413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015230019079674749892275 4522845028619512124838413)
          ·
            refine ⟨1696066885732317046814405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4522845028619512124838413 1696066885732317046814405)
            ·
              refine ⟨318012541074809446277701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1696066885732317046814405 318012541074809446277701)
              ·
                refine ⟨59627351451526771177069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318012541074809446277701 59627351451526771177069)
                ·
                  rfl

theorem cell20_391918_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_391918 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391918 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391918 prefixEnd_391918 := by exact prefixLift 391918
  have htrace : WordTrace (prefixWord ++ tailWord_391918) baseStart_391918 baseEnd_391918 := by
    simpa [prefixWord, tailWord_391918, baseEnd_391918] using wordTrace_append hprefix tailTrace_391918
  have hstable : (prefixWord ++ tailWord_391918).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391918).length < 2 ^ (prefixWord ++ tailWord_391918).sum := by decide
  have hdescent : baseEnd_391918 < baseStart_391918 := by decide
  rcases family_descends (prefixWord ++ tailWord_391918) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391946 : List Nat := [3, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_391946 : Nat := 118140960795 + 391946 * 2 ^ 59
def prefixEnd_391946 : Nat := 4983230072969 + 3 ^ 40 * 391946 * 2
def baseEnd_391946 : Nat := 178894834317536660597759

theorem tailTrace_391946 : CollatzResearch.WordTrace tailWord_391946 prefixEnd_391946 178894834317536660597759 := by
  unfold tailWord_391946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3573861259513513973154923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9530296692036037261746461 3573861259513513973154923)
  ·
    refine ⟨5360791889270270959732385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3573861259513513973154923 5360791889270270959732385)
    ·
      refine ⟨4020593916952703219799289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5360791889270270959732385 4020593916952703219799289)
      ·
        refine ⟨3015445437714527414849467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4020593916952703219799289 3015445437714527414849467)
        ·
          refine ⟨4523168156571791122274201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3015445437714527414849467 4523168156571791122274201)
          ·
            refine ⟨3392376117428843341705651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4523168156571791122274201 3392376117428843341705651)
            ·
              refine ⟨5088564176143265012558477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3392376117428843341705651 5088564176143265012558477)
              ·
                refine ⟨1908211566053724379709429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5088564176143265012558477 1908211566053724379709429)
                ·
                  refine ⟨178894834317536660597759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1908211566053724379709429 178894834317536660597759)
                  ·
                    rfl

theorem cell20_391946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_391946 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391946 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391946 prefixEnd_391946 := by exact prefixLift 391946
  have htrace : WordTrace (prefixWord ++ tailWord_391946) baseStart_391946 baseEnd_391946 := by
    simpa [prefixWord, tailWord_391946, baseEnd_391946] using wordTrace_append hprefix tailTrace_391946
  have hstable : (prefixWord ++ tailWord_391946).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391946).length < 2 ^ (prefixWord ++ tailWord_391946).sum := by decide
  have hdescent : baseEnd_391946 < baseStart_391946 := by decide
  rcases family_descends (prefixWord ++ tailWord_391946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_391959 : List Nat := [1, 1, 3, 4, 3, 2, 2, 1, 3]
def baseStart_391959 : Nat := 118140960795 + 391959 * 2 ^ 59
def prefixEnd_391959 : Nat := 4983230072969 + 3 ^ 40 * 391959 * 2
def baseEnd_391959 : Nat := 178900767871766393164373

theorem tailTrace_391959 : CollatzResearch.WordTrace tailWord_391959 prefixEnd_391959 178900767871766393164373 := by
  unfold tailWord_391959
  simp only [CollatzResearch.WordTrace]
  refine ⟨14295919187006959112842931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9530612791337972741895287 14295919187006959112842931)
  ·
    refine ⟨21443878780510438669264397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14295919187006959112842931 21443878780510438669264397)
    ·
      refine ⟨8041454542691414500974149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21443878780510438669264397 8041454542691414500974149)
      ·
        refine ⟨1507772726754640218932653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8041454542691414500974149 1507772726754640218932653)
        ·
          refine ⟨565414772532990082099745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1507772726754640218932653 565414772532990082099745)
          ·
            refine ⟨424061079399742561574809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 565414772532990082099745 424061079399742561574809)
            ·
              refine ⟨318045809549806921181107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424061079399742561574809 318045809549806921181107)
              ·
                refine ⟨477068714324710381771661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318045809549806921181107 477068714324710381771661)
                ·
                  refine ⟨178900767871766393164373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477068714324710381771661 178900767871766393164373)
                  ·
                    rfl

theorem cell20_391959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3].length) (baseStart_391959 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_391959 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_391959 prefixEnd_391959 := by exact prefixLift 391959
  have htrace : WordTrace (prefixWord ++ tailWord_391959) baseStart_391959 baseEnd_391959 := by
    simpa [prefixWord, tailWord_391959, baseEnd_391959] using wordTrace_append hprefix tailTrace_391959
  have hstable : (prefixWord ++ tailWord_391959).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_391959).length < 2 ^ (prefixWord ++ tailWord_391959).sum := by decide
  have hdescent : baseEnd_391959 < baseStart_391959 := by decide
  rcases family_descends (prefixWord ++ tailWord_391959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392053 : List Nat := [1, 3, 4, 1, 1, 3, 7]
def baseStart_392053 : Nat := 118140960795 + 392053 * 2 ^ 59
def prefixEnd_392053 : Nat := 4983230072969 + 3 ^ 40 * 392053 * 2
def baseEnd_392053 : Nat := 19882630225902204892295

theorem tailTrace_392053 : CollatzResearch.WordTrace tailWord_392053 prefixEnd_392053 19882630225902204892295 := by
  unfold tailWord_392053
  simp only [CollatzResearch.WordTrace]
  refine ⟨14299347648666413166764813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9532898432444275444509875 14299347648666413166764813)
  ·
    refine ⟨5362255368249904937536805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14299347648666413166764813 5362255368249904937536805)
    ·
      refine ⟨1005422881546857175788151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5362255368249904937536805 1005422881546857175788151)
      ·
        refine ⟨1508134322320285763682227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005422881546857175788151 1508134322320285763682227)
        ·
          refine ⟨2262201483480428645523341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508134322320285763682227 2262201483480428645523341)
          ·
            refine ⟨848325556305160742071253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2262201483480428645523341 848325556305160742071253)
            ·
              refine ⟨19882630225902204892295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 848325556305160742071253 19882630225902204892295)
              ·
                rfl

theorem cell20_392053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 3, 7].length) (baseStart_392053 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392053 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392053 prefixEnd_392053 := by exact prefixLift 392053
  have htrace : WordTrace (prefixWord ++ tailWord_392053) baseStart_392053 baseEnd_392053 := by
    simpa [prefixWord, tailWord_392053, baseEnd_392053] using wordTrace_append hprefix tailTrace_392053
  have hstable : (prefixWord ++ tailWord_392053).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392053).length < 2 ^ (prefixWord ++ tailWord_392053).sum := by decide
  have hdescent : baseEnd_392053 < baseStart_392053 := by decide
  rcases family_descends (prefixWord ++ tailWord_392053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392084 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 4]
def baseStart_392084 : Nat := 118140960795 + 392084 * 2 ^ 59
def prefixEnd_392084 : Nat := 4983230072969 + 3 ^ 40 * 392084 * 2
def baseEnd_392084 : Nat := 178957821277821513997195

theorem tailTrace_392084 : CollatzResearch.WordTrace tailWord_392084 prefixEnd_392084 178957821277821513997195 := by
  unfold tailWord_392084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7150239155777052730571653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9533652207702736974095537 7150239155777052730571653)
  ·
    refine ⟨1340669841708197386982185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7150239155777052730571653 1340669841708197386982185)
    ·
      refine ⟨1005502381281148040236639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1340669841708197386982185 1005502381281148040236639)
      ·
        refine ⟨1508253571921722060354959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1005502381281148040236639 1508253571921722060354959)
        ·
          refine ⟨2262380357882583090532439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1508253571921722060354959 2262380357882583090532439)
          ·
            refine ⟨3393570536823874635798659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2262380357882583090532439 3393570536823874635798659)
            ·
              refine ⟨5090355805235811953697989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3393570536823874635798659 5090355805235811953697989)
              ·
                refine ⟨954441713481714741318373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5090355805235811953697989 954441713481714741318373)
                ·
                  refine ⟨178957821277821513997195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954441713481714741318373 178957821277821513997195)
                  ·
                    rfl

theorem cell20_392084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_392084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392084 prefixEnd_392084 := by exact prefixLift 392084
  have htrace : WordTrace (prefixWord ++ tailWord_392084) baseStart_392084 baseEnd_392084 := by
    simpa [prefixWord, tailWord_392084, baseEnd_392084] using wordTrace_append hprefix tailTrace_392084
  have hstable : (prefixWord ++ tailWord_392084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392084).length < 2 ^ (prefixWord ++ tailWord_392084).sum := by decide
  have hdescent : baseEnd_392084 < baseStart_392084 := by decide
  rcases family_descends (prefixWord ++ tailWord_392084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392177 : List Nat := [1, 2, 2, 2, 4, 2, 1, 4, 2]
def baseStart_392177 : Nat := 118140960795 + 392177 * 2 ^ 59
def prefixEnd_392177 : Nat := 4983230072969 + 3 ^ 40 * 392177 * 2
def baseEnd_392177 : Nat := 179000269011926523896815

theorem tailTrace_392177 : CollatzResearch.WordTrace tailWord_392177 prefixEnd_392177 179000269011926523896815 := by
  unfold tailWord_392177
  simp only [CollatzResearch.WordTrace]
  refine ⟨14303870300217182344278785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9535913533478121562852523 14303870300217182344278785)
  ·
    refine ⟨10727902725162886758209089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14303870300217182344278785 10727902725162886758209089)
    ·
      refine ⟨8045927043872165068656817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10727902725162886758209089 8045927043872165068656817)
      ·
        refine ⟨6034445282904123801492613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8045927043872165068656817 6034445282904123801492613)
        ·
          refine ⟨1131458490544523212779865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6034445282904123801492613 1131458490544523212779865)
          ·
            refine ⟨848593867908392409584899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131458490544523212779865 848593867908392409584899)
            ·
              refine ⟨1272890801862588614377349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848593867908392409584899 1272890801862588614377349)
              ·
                refine ⟨238667025349235365195753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1272890801862588614377349 238667025349235365195753)
                ·
                  refine ⟨179000269011926523896815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238667025349235365195753 179000269011926523896815)
                  ·
                    rfl

theorem cell20_392177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 4, 2].length) (baseStart_392177 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392177 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392177 prefixEnd_392177 := by exact prefixLift 392177
  have htrace : WordTrace (prefixWord ++ tailWord_392177) baseStart_392177 baseEnd_392177 := by
    simpa [prefixWord, tailWord_392177, baseEnd_392177] using wordTrace_append hprefix tailTrace_392177
  have hstable : (prefixWord ++ tailWord_392177).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392177).length < 2 ^ (prefixWord ++ tailWord_392177).sum := by decide
  have hdescent : baseEnd_392177 < baseStart_392177 := by decide
  rcases family_descends (prefixWord ++ tailWord_392177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392194 : List Nat := [3, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_392194 : Nat := 118140960795 + 392194 * 2 ^ 59
def prefixEnd_392194 : Nat := 4983230072969 + 3 ^ 40 * 392194 * 2
def baseEnd_392194 : Nat := 179008028275150020330079

theorem tailTrace_392194 : CollatzResearch.WordTrace tailWord_392194 prefixEnd_392194 179008028275150020330079 := by
  unfold tailWord_392194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576122585288898561911909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9536326894103729498431757 3576122585288898561911909)
  ·
    refine ⟨670522984741668480358483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3576122585288898561911909 670522984741668480358483)
    ·
      refine ⟨1005784477112502720537725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670522984741668480358483 1005784477112502720537725)
      ·
        refine ⟨377169178917188520201647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1005784477112502720537725 377169178917188520201647)
        ·
          refine ⟨565753768375782780302471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377169178917188520201647 565753768375782780302471)
          ·
            refine ⟨848630652563674170453707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 565753768375782780302471 848630652563674170453707)
            ·
              refine ⟨1272945978845511255680561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 848630652563674170453707 1272945978845511255680561)
              ·
                refine ⟨954709484134133441760421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1272945978845511255680561 954709484134133441760421)
                ·
                  refine ⟨179008028275150020330079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 954709484134133441760421 179008028275150020330079)
                  ·
                    rfl

theorem cell20_392194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_392194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392194 prefixEnd_392194 := by exact prefixLift 392194
  have htrace : WordTrace (prefixWord ++ tailWord_392194) baseStart_392194 baseEnd_392194 := by
    simpa [prefixWord, tailWord_392194, baseEnd_392194] using wordTrace_append hprefix tailTrace_392194
  have hstable : (prefixWord ++ tailWord_392194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392194).length < 2 ^ (prefixWord ++ tailWord_392194).sum := by decide
  have hdescent : baseEnd_392194 < baseStart_392194 := by decide
  rcases family_descends (prefixWord ++ tailWord_392194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392195 : List Nat := [1, 1, 1, 3, 2, 1, 1, 1, 9]
def baseStart_392195 : Nat := 118140960795 + 392195 * 2 ^ 59
def prefixEnd_392195 : Nat := 4983230072969 + 3 ^ 40 * 392195 * 2
def baseEnd_392195 : Nat := 179008484702398461296741

theorem tailTrace_392195 : CollatzResearch.WordTrace tailWord_392195 prefixEnd_392195 179008484702398461296741 := by
  unfold tailWord_392195
  simp only [CollatzResearch.WordTrace]
  refine ⟨14304526814151971418434039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9536351209434647612289359 14304526814151971418434039)
  ·
    refine ⟨21456790221227957127651059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14304526814151971418434039 21456790221227957127651059)
    ·
      refine ⟨32185185331841935691476589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21456790221227957127651059 32185185331841935691476589)
      ·
        refine ⟨12069444499440725884303721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 32185185331841935691476589 12069444499440725884303721)
        ·
          refine ⟨9052083374580544413227791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12069444499440725884303721 9052083374580544413227791)
          ·
            refine ⟨13578125061870816619841687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9052083374580544413227791 13578125061870816619841687)
            ·
              refine ⟨20367187592806224929762531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13578125061870816619841687 20367187592806224929762531)
              ·
                refine ⟨30550781389209337394643797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20367187592806224929762531 30550781389209337394643797)
                ·
                  refine ⟨179008484702398461296741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30550781389209337394643797 179008484702398461296741)
                  ·
                    rfl

theorem cell20_392195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 1, 1, 9].length) (baseStart_392195 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392195 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392195 prefixEnd_392195 := by exact prefixLift 392195
  have htrace : WordTrace (prefixWord ++ tailWord_392195) baseStart_392195 baseEnd_392195 := by
    simpa [prefixWord, tailWord_392195, baseEnd_392195] using wordTrace_append hprefix tailTrace_392195
  have hstable : (prefixWord ++ tailWord_392195).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392195).length < 2 ^ (prefixWord ++ tailWord_392195).sum := by decide
  have hdescent : baseEnd_392195 < baseStart_392195 := by decide
  rcases family_descends (prefixWord ++ tailWord_392195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392215 : List Nat := [1, 1, 3, 5, 1, 1, 1, 5, 2]
def baseStart_392215 : Nat := 118140960795 + 392215 * 2 ^ 59
def prefixEnd_392215 : Nat := 4983230072969 + 3 ^ 40 * 392215 * 2
def baseEnd_392215 : Nat := 179017613247367280629993

theorem tailTrace_392215 : CollatzResearch.WordTrace tailWord_392215 prefixEnd_392215 179017613247367280629993 := by
  unfold tailWord_392215
  simp only [CollatzResearch.WordTrace]
  refine ⟨14305256274079514834162099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9536837516053009889441399 14305256274079514834162099)
  ·
    refine ⟨21457884411119272251243149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14305256274079514834162099 21457884411119272251243149)
    ·
      refine ⟨8046706654169727094216181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21457884411119272251243149 8046706654169727094216181)
      ·
        refine ⟨754378748828411915082767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8046706654169727094216181 754378748828411915082767)
        ·
          refine ⟨1131568123242617872624151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754378748828411915082767 1131568123242617872624151)
          ·
            refine ⟨1697352184863926808936227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131568123242617872624151 1697352184863926808936227)
            ·
              refine ⟨2546028277295890213404341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1697352184863926808936227 2546028277295890213404341)
              ·
                refine ⟨238690150996489707506657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2546028277295890213404341 238690150996489707506657)
                ·
                  refine ⟨179017613247367280629993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238690150996489707506657 179017613247367280629993)
                  ·
                    rfl

theorem cell20_392215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 5, 2].length) (baseStart_392215 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392215 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392215 prefixEnd_392215 := by exact prefixLift 392215
  have htrace : WordTrace (prefixWord ++ tailWord_392215) baseStart_392215 baseEnd_392215 := by
    simpa [prefixWord, tailWord_392215, baseEnd_392215] using wordTrace_append hprefix tailTrace_392215
  have hstable : (prefixWord ++ tailWord_392215).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392215).length < 2 ^ (prefixWord ++ tailWord_392215).sum := by decide
  have hdescent : baseEnd_392215 < baseStart_392215 := by decide
  rcases family_descends (prefixWord ++ tailWord_392215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392236 : List Nat := [2, 2, 1, 1, 1, 2, 3, 6, 2]
def baseStart_392236 : Nat := 118140960795 + 392236 * 2 ^ 59
def prefixEnd_392236 : Nat := 4983230072969 + 3 ^ 40 * 392236 * 2
def baseEnd_392236 : Nat := 179027198219584540929907

theorem tailTrace_392236 : CollatzResearch.WordTrace tailWord_392236 prefixEnd_392236 179027198219584540929907 := by
  unfold tailWord_392236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153011103501717710338281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9537348138002290280451041 7153011103501717710338281)
  ·
    refine ⟨5364758327626288282753711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7153011103501717710338281 5364758327626288282753711)
    ·
      refine ⟨8047137491439432424130567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364758327626288282753711 8047137491439432424130567)
      ·
        refine ⟨12070706237159148636195851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047137491439432424130567 12070706237159148636195851)
        ·
          refine ⟨18106059355738722954293777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12070706237159148636195851 18106059355738722954293777)
          ·
            refine ⟨13579544516804042215720333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18106059355738722954293777 13579544516804042215720333)
            ·
              refine ⟨5092329193801515830895125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13579544516804042215720333 5092329193801515830895125)
              ·
                refine ⟨238702930959446054573209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5092329193801515830895125 238702930959446054573209)
                ·
                  refine ⟨179027198219584540929907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238702930959446054573209 179027198219584540929907)
                  ·
                    rfl

theorem cell20_392236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 6, 2].length) (baseStart_392236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392236 prefixEnd_392236 := by exact prefixLift 392236
  have htrace : WordTrace (prefixWord ++ tailWord_392236) baseStart_392236 baseEnd_392236 := by
    simpa [prefixWord, tailWord_392236, baseEnd_392236] using wordTrace_append hprefix tailTrace_392236
  have hstable : (prefixWord ++ tailWord_392236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392236).length < 2 ^ (prefixWord ++ tailWord_392236).sum := by decide
  have hdescent : baseEnd_392236 < baseStart_392236 := by decide
  rcases family_descends (prefixWord ++ tailWord_392236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392250 : List Nat := [3, 1, 1, 1, 3, 1, 2, 5, 3]
def baseStart_392250 : Nat := 118140960795 + 392250 * 2 ^ 59
def prefixEnd_392250 : Nat := 4983230072969 + 3 ^ 40 * 392250 * 2
def baseEnd_392250 : Nat := 179033588201062714463183

theorem tailTrace_392250 : CollatzResearch.WordTrace tailWord_392250 prefixEnd_392250 179033588201062714463183 := by
  unfold tailWord_392250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3576633207238178952921551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9537688552635143874457469 3576633207238178952921551)
  ·
    refine ⟨5364949810857268429382327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3576633207238178952921551 5364949810857268429382327)
    ·
      refine ⟨8047424716285902644073491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5364949810857268429382327 8047424716285902644073491)
      ·
        refine ⟨12071137074428853966110237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8047424716285902644073491 12071137074428853966110237)
        ·
          refine ⟨4526676402910820237291339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12071137074428853966110237 4526676402910820237291339)
          ·
            refine ⟨6790014604366230355937009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4526676402910820237291339 6790014604366230355937009)
            ·
              refine ⟨5092510953274672766952757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6790014604366230355937009 5092510953274672766952757)
              ·
                refine ⟨477422901869500571901821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5092510953274672766952757 477422901869500571901821)
                ·
                  refine ⟨179033588201062714463183, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477422901869500571901821 179033588201062714463183)
                  ·
                    rfl

theorem cell20_392250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 5, 3].length) (baseStart_392250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392250 prefixEnd_392250 := by exact prefixLift 392250
  have htrace : WordTrace (prefixWord ++ tailWord_392250) baseStart_392250 baseEnd_392250 := by
    simpa [prefixWord, tailWord_392250, baseEnd_392250] using wordTrace_append hprefix tailTrace_392250
  have hstable : (prefixWord ++ tailWord_392250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392250).length < 2 ^ (prefixWord ++ tailWord_392250).sum := by decide
  have hdescent : baseEnd_392250 < baseStart_392250 := by decide
  rcases family_descends (prefixWord ++ tailWord_392250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392264 : List Nat := [2, 1, 3, 1, 1, 1, 5, 6]
def baseStart_392264 : Nat := 118140960795 + 392264 * 2 ^ 59
def prefixEnd_392264 : Nat := 4983230072969 + 3 ^ 40 * 392264 * 2
def baseEnd_392264 : Nat := 59679992727513629332153

theorem tailTrace_392264 : CollatzResearch.WordTrace tailWord_392264 prefixEnd_392264 59679992727513629332153 := by
  unfold tailWord_392264
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153521725450998101347923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9538028967267997468463897 7153521725450998101347923)
  ·
    refine ⟨10730282588176497152021885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7153521725450998101347923 10730282588176497152021885)
    ·
      refine ⟨4023855970566186432008207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10730282588176497152021885 4023855970566186432008207)
      ·
        refine ⟨6035783955849279648012311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4023855970566186432008207 6035783955849279648012311)
        ·
          refine ⟨9053675933773919472018467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6035783955849279648012311 9053675933773919472018467)
          ·
            refine ⟨13580513900660879208027701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9053675933773919472018467 13580513900660879208027701)
            ·
              refine ⟨1273173178186957425752597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 13580513900660879208027701 1273173178186957425752597)
              ·
                refine ⟨59679992727513629332153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1273173178186957425752597 59679992727513629332153)
                ·
                  rfl

theorem cell20_392264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 5, 6].length) (baseStart_392264 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392264 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392264 prefixEnd_392264 := by exact prefixLift 392264
  have htrace : WordTrace (prefixWord ++ tailWord_392264) baseStart_392264 baseEnd_392264 := by
    simpa [prefixWord, tailWord_392264, baseEnd_392264] using wordTrace_append hprefix tailTrace_392264
  have hstable : (prefixWord ++ tailWord_392264).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392264).length < 2 ^ (prefixWord ++ tailWord_392264).sum := by decide
  have hdescent : baseEnd_392264 < baseStart_392264 := by decide
  rcases family_descends (prefixWord ++ tailWord_392264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392288 : List Nat := [2, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_392288 : Nat := 118140960795 + 392288 * 2 ^ 59
def prefixEnd_392288 : Nat := 4983230072969 + 3 ^ 40 * 392288 * 2
def baseEnd_392288 : Nat := 179050932436503471196361

theorem tailTrace_392288 : CollatzResearch.WordTrace tailWord_392288 prefixEnd_392288 179050932436503471196361 := by
  unfold tailWord_392288
  simp only [CollatzResearch.WordTrace]
  refine ⟨7153959401407524150784759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9538612535210032201046345 7153959401407524150784759)
  ·
    refine ⟨10730939102111286226177139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7153959401407524150784759 10730939102111286226177139)
    ·
      refine ⟨16096408653166929339265709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10730939102111286226177139 16096408653166929339265709)
      ·
        refine ⟨6036153244937598502224641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16096408653166929339265709 6036153244937598502224641)
        ·
          refine ⟨4527114933703198876668481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6036153244937598502224641 4527114933703198876668481)
          ·
            refine ⟨3395336200277399157501361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4527114933703198876668481 3395336200277399157501361)
            ·
              refine ⟨2546502150208049368126021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3395336200277399157501361 2546502150208049368126021)
              ·
                refine ⟨477469153164009256523629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2546502150208049368126021 477469153164009256523629)
                ·
                  refine ⟨179050932436503471196361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477469153164009256523629 179050932436503471196361)
                  ·
                    rfl

theorem cell20_392288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_392288 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392288 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392288 prefixEnd_392288 := by exact prefixLift 392288
  have htrace : WordTrace (prefixWord ++ tailWord_392288) baseStart_392288 baseEnd_392288 := by
    simpa [prefixWord, tailWord_392288, baseEnd_392288] using wordTrace_append hprefix tailTrace_392288
  have hstable : (prefixWord ++ tailWord_392288).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392288).length < 2 ^ (prefixWord ++ tailWord_392288).sum := by decide
  have hdescent : baseEnd_392288 < baseStart_392288 := by decide
  rcases family_descends (prefixWord ++ tailWord_392288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392340 : List Nat := [2, 4, 2, 12]
def baseStart_392340 : Nat := 118140960795 + 392340 * 2 ^ 59
def prefixEnd_392340 : Nat := 4983230072969 + 3 ^ 40 * 392340 * 2
def baseEnd_392340 : Nat := 736932784581985191205

theorem tailTrace_392340 : CollatzResearch.WordTrace tailWord_392340 prefixEnd_392340 736932784581985191205 := by
  unfold tailWord_392340
  simp only [CollatzResearch.WordTrace]
  refine ⟨7154907699313330591231237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9539876932417774121641649 7154907699313330591231237)
  ·
    refine ⟨1341545193621249485855857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7154907699313330591231237 1341545193621249485855857)
    ·
      refine ⟨1006158895215937114391893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1341545193621249485855857 1006158895215937114391893)
      ·
        refine ⟨736932784581985191205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 1006158895215937114391893 736932784581985191205)
        ·
          rfl

theorem cell20_392340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 12].length) (baseStart_392340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392340 prefixEnd_392340 := by exact prefixLift 392340
  have htrace : WordTrace (prefixWord ++ tailWord_392340) baseStart_392340 baseEnd_392340 := by
    simpa [prefixWord, tailWord_392340, baseEnd_392340] using wordTrace_append hprefix tailTrace_392340
  have hstable : (prefixWord ++ tailWord_392340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392340).length < 2 ^ (prefixWord ++ tailWord_392340).sum := by decide
  have hdescent : baseEnd_392340 < baseStart_392340 := by decide
  rcases family_descends (prefixWord ++ tailWord_392340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392343 : List Nat := [1, 1, 3, 3, 3, 2, 2, 2, 3]
def baseStart_392343 : Nat := 118140960795 + 392343 * 2 ^ 59
def prefixEnd_392343 : Nat := 4983230072969 + 3 ^ 40 * 392343 * 2
def baseEnd_392343 : Nat := 179076035935167724362803

theorem tailTrace_392343 : CollatzResearch.WordTrace tailWord_392343 prefixEnd_392343 179076035935167724362803 := by
  unfold tailWord_392343
  simp only [CollatzResearch.WordTrace]
  refine ⟨14309924817615792694821683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9539949878410528463214455 14309924817615792694821683)
  ·
    refine ⟨21464887226423689042232525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14309924817615792694821683 21464887226423689042232525)
    ·
      refine ⟨8049332709908883390837197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21464887226423689042232525 8049332709908883390837197)
      ·
        refine ⟨3018499766215831271563949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8049332709908883390837197 3018499766215831271563949)
        ·
          refine ⟨1131937412330936726836481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3018499766215831271563949 1131937412330936726836481)
          ·
            refine ⟨848953059248202545127361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1131937412330936726836481 848953059248202545127361)
            ·
              refine ⟨636714794436151908845521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 848953059248202545127361 636714794436151908845521)
              ·
                refine ⟨477536095827113931634141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636714794436151908845521 477536095827113931634141)
                ·
                  refine ⟨179076035935167724362803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477536095827113931634141 179076035935167724362803)
                  ·
                    rfl

theorem cell20_392343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 2, 2, 3].length) (baseStart_392343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392343 prefixEnd_392343 := by exact prefixLift 392343
  have htrace : WordTrace (prefixWord ++ tailWord_392343) baseStart_392343 baseEnd_392343 := by
    simpa [prefixWord, tailWord_392343, baseEnd_392343] using wordTrace_append hprefix tailTrace_392343
  have hstable : (prefixWord ++ tailWord_392343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392343).length < 2 ^ (prefixWord ++ tailWord_392343).sum := by decide
  have hdescent : baseEnd_392343 < baseStart_392343 := by decide
  rcases family_descends (prefixWord ++ tailWord_392343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392346 : List Nat := [3, 1, 1, 5, 1, 1, 4, 2, 2]
def baseStart_392346 : Nat := 118140960795 + 392346 * 2 ^ 59
def prefixEnd_392346 : Nat := 4983230072969 + 3 ^ 40 * 392346 * 2
def baseEnd_392346 : Nat := 179077405216913047262791

theorem tailTrace_392346 : CollatzResearch.WordTrace tailWord_392346 prefixEnd_392346 179077405216913047262791 := by
  unfold tailWord_392346
  simp only [CollatzResearch.WordTrace]
  refine ⟨3577508559151231051795223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9540022824403282804787261 3577508559151231051795223)
  ·
    refine ⟨5366262838726846577692835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3577508559151231051795223 5366262838726846577692835)
    ·
      refine ⟨8049394258090269866539253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366262838726846577692835 8049394258090269866539253)
      ·
        refine ⟨754630711695962799988055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8049394258090269866539253 754630711695962799988055)
        ·
          refine ⟨1131946067543944199982083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754630711695962799988055 1131946067543944199982083)
          ·
            refine ⟨1697919101315916299973125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1131946067543944199982083 1697919101315916299973125)
            ·
              refine ⟨318359831496734306244961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1697919101315916299973125 318359831496734306244961)
              ·
                refine ⟨238769873622550729683721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318359831496734306244961 238769873622550729683721)
                ·
                  refine ⟨179077405216913047262791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238769873622550729683721 179077405216913047262791)
                  ·
                    rfl

theorem cell20_392346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 4, 2, 2].length) (baseStart_392346 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392346 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392346 prefixEnd_392346 := by exact prefixLift 392346
  have htrace : WordTrace (prefixWord ++ tailWord_392346) baseStart_392346 baseEnd_392346 := by
    simpa [prefixWord, tailWord_392346, baseEnd_392346] using wordTrace_append hprefix tailTrace_392346
  have hstable : (prefixWord ++ tailWord_392346).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392346).length < 2 ^ (prefixWord ++ tailWord_392346).sum := by decide
  have hdescent : baseEnd_392346 < baseStart_392346 := by decide
  rcases family_descends (prefixWord ++ tailWord_392346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392357 : List Nat := [1, 3, 1, 2, 1, 6, 1, 5]
def baseStart_392357 : Nat := 118140960795 + 392357 * 2 ^ 59
def prefixEnd_392357 : Nat := 4983230072969 + 3 ^ 40 * 392357 * 2
def baseEnd_392357 : Nat := 59694141972215299298693

theorem tailTrace_392357 : CollatzResearch.WordTrace tailWord_392357 prefixEnd_392357 59694141972215299298693 := by
  unfold tailWord_392357
  simp only [CollatzResearch.WordTrace]
  refine ⟨14310435439565073085831325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9540290293043382057220883 14310435439565073085831325)
  ·
    refine ⟨5366413289836902407186747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14310435439565073085831325 5366413289836902407186747)
    ·
      refine ⟨8049619934755353610780121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5366413289836902407186747 8049619934755353610780121)
      ·
        refine ⟨6037214951066515208085091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8049619934755353610780121 6037214951066515208085091)
        ·
          refine ⟨9055822426599772812127637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6037214951066515208085091 9055822426599772812127637)
          ·
            refine ⟨424491676246864350568483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9055822426599772812127637 424491676246864350568483)
            ·
              refine ⟨636737514370296525852725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424491676246864350568483 636737514370296525852725)
              ·
                refine ⟨59694141972215299298693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 636737514370296525852725 59694141972215299298693)
                ·
                  rfl

theorem cell20_392357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 6, 1, 5].length) (baseStart_392357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392357 prefixEnd_392357 := by exact prefixLift 392357
  have htrace : WordTrace (prefixWord ++ tailWord_392357) baseStart_392357 baseEnd_392357 := by
    simpa [prefixWord, tailWord_392357, baseEnd_392357] using wordTrace_append hprefix tailTrace_392357
  have hstable : (prefixWord ++ tailWord_392357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392357).length < 2 ^ (prefixWord ++ tailWord_392357).sum := by decide
  have hdescent : baseEnd_392357 < baseStart_392357 := by decide
  rcases family_descends (prefixWord ++ tailWord_392357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392398 : List Nat := [4, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_392398 : Nat := 118140960795 + 392398 * 2 ^ 59
def prefixEnd_392398 : Nat := 4983230072969 + 3 ^ 40 * 392398 * 2
def baseEnd_392398 : Nat := 179101139433831977529245

theorem tailTrace_392398 : CollatzResearch.WordTrace tailWord_392398 prefixEnd_392398 179101139433831977529245 := by
  unfold tailWord_392398
  simp only [CollatzResearch.WordTrace]
  refine ⟨1788991354052067136009231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9541287221611024725382565 1788991354052067136009231)
  ·
    refine ⟨2683487031078100704013847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1788991354052067136009231 2683487031078100704013847)
    ·
      refine ⟨4025230546617151056020771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2683487031078100704013847 4025230546617151056020771)
      ·
        refine ⟨6037845819925726584031157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4025230546617151056020771 6037845819925726584031157)
        ·
          refine ⟨566048045618036867252921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6037845819925726584031157 566048045618036867252921)
          ·
            refine ⟨424536034213527650439691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566048045618036867252921 424536034213527650439691)
            ·
              refine ⟨636804051320291475659537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424536034213527650439691 636804051320291475659537)
              ·
                refine ⟨477603038490218606744653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 636804051320291475659537 477603038490218606744653)
                ·
                  refine ⟨179101139433831977529245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477603038490218606744653 179101139433831977529245)
                  ·
                    rfl

theorem cell20_392398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_392398 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392398 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392398 prefixEnd_392398 := by exact prefixLift 392398
  have htrace : WordTrace (prefixWord ++ tailWord_392398) baseStart_392398 baseEnd_392398 := by
    simpa [prefixWord, tailWord_392398, baseEnd_392398] using wordTrace_append hprefix tailTrace_392398
  have hstable : (prefixWord ++ tailWord_392398).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392398).length < 2 ^ (prefixWord ++ tailWord_392398).sum := by decide
  have hdescent : baseEnd_392398 < baseStart_392398 := by decide
  rcases family_descends (prefixWord ++ tailWord_392398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392402 : List Nat := [3, 2, 2, 2, 1, 1, 3, 1, 5]
def baseStart_392402 : Nat := 118140960795 + 392402 * 2 ^ 59
def prefixEnd_392402 : Nat := 4983230072969 + 3 ^ 40 * 392402 * 2
def baseEnd_392402 : Nat := 179102965142825741395895

theorem tailTrace_392402 : CollatzResearch.WordTrace tailWord_392402 prefixEnd_392402 179102965142825741395895 := by
  unfold tailWord_392402
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578019181100511442804865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9541384482934697180812973 3578019181100511442804865)
  ·
    refine ⟨2683514385825383582103649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3578019181100511442804865 2683514385825383582103649)
    ·
      refine ⟨2012635789369037686577737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2683514385825383582103649 2012635789369037686577737)
      ·
        refine ⟨1509476842026778264933303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2012635789369037686577737 1509476842026778264933303)
        ·
          refine ⟨2264215263040167397399955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1509476842026778264933303 2264215263040167397399955)
          ·
            refine ⟨3396322894560251096099933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2264215263040167397399955 3396322894560251096099933)
            ·
              refine ⟨1273621085460094161037475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3396322894560251096099933 1273621085460094161037475)
              ·
                refine ⟨1910431628190141241556213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1273621085460094161037475 1910431628190141241556213)
                ·
                  refine ⟨179102965142825741395895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1910431628190141241556213 179102965142825741395895)
                  ·
                    rfl

theorem cell20_392402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 3, 1, 5].length) (baseStart_392402 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392402 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392402 prefixEnd_392402 := by exact prefixLift 392402
  have htrace : WordTrace (prefixWord ++ tailWord_392402) baseStart_392402 baseEnd_392402 := by
    simpa [prefixWord, tailWord_392402, baseEnd_392402] using wordTrace_append hprefix tailTrace_392402
  have hstable : (prefixWord ++ tailWord_392402).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392402).length < 2 ^ (prefixWord ++ tailWord_392402).sum := by decide
  have hdescent : baseEnd_392402 < baseStart_392402 := by decide
  rcases family_descends (prefixWord ++ tailWord_392402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392405 : List Nat := [1, 3, 2, 4, 1, 1, 2, 4, 2]
def baseStart_392405 : Nat := 118140960795 + 392405 * 2 ^ 59
def prefixEnd_392405 : Nat := 4983230072969 + 3 ^ 40 * 392405 * 2
def baseEnd_392405 : Nat := 179104334424571064295883

theorem tailTrace_392405 : CollatzResearch.WordTrace tailWord_392405 prefixEnd_392405 179104334424571064295883 := by
  unfold tailWord_392405
  simp only [CollatzResearch.WordTrace]
  refine ⟨14312186143391177283578669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9541457428927451522385779 14312186143391177283578669)
  ·
    refine ⟨5367069803771691481342001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14312186143391177283578669 5367069803771691481342001)
    ·
      refine ⟨4025302352828768611006501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5367069803771691481342001 4025302352828768611006501)
      ·
        refine ⟨754744191155394114563719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4025302352828768611006501 754744191155394114563719)
        ·
          refine ⟨1132116286733091171845579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 754744191155394114563719 1132116286733091171845579)
          ·
            refine ⟨1698174430099636757768369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1132116286733091171845579 1698174430099636757768369)
            ·
              refine ⟨1273630822574727568326277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1698174430099636757768369 1273630822574727568326277)
              ·
                refine ⟨238805779232761419061177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1273630822574727568326277 238805779232761419061177)
                ·
                  refine ⟨179104334424571064295883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238805779232761419061177 179104334424571064295883)
                  ·
                    rfl

theorem cell20_392405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_392405 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392405 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392405 prefixEnd_392405 := by exact prefixLift 392405
  have htrace : WordTrace (prefixWord ++ tailWord_392405) baseStart_392405 baseEnd_392405 := by
    simpa [prefixWord, tailWord_392405, baseEnd_392405] using wordTrace_append hprefix tailTrace_392405
  have hstable : (prefixWord ++ tailWord_392405).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392405).length < 2 ^ (prefixWord ++ tailWord_392405).sum := by decide
  have hdescent : baseEnd_392405 < baseStart_392405 := by decide
  rcases family_descends (prefixWord ++ tailWord_392405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392450 : List Nat := [3, 4, 1, 1, 3, 2, 6]
def baseStart_392450 : Nat := 118140960795 + 392450 * 2 ^ 59
def prefixEnd_392450 : Nat := 4983230072969 + 3 ^ 40 * 392450 * 2
def baseEnd_392450 : Nat := 19902763738972323088411

theorem tailTrace_392450 : CollatzResearch.WordTrace tailWord_392450 prefixEnd_392450 19902763738972323088411 := by
  unfold tailWord_392450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578456857057037492241701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9542551618818766645977869 3578456857057037492241701)
  ·
    refine ⟨670960660698194529795319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3578456857057037492241701 670960660698194529795319)
    ·
      refine ⟨1006440991047291794692979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 670960660698194529795319 1006440991047291794692979)
      ·
        refine ⟨1509661486570937692039469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1006440991047291794692979 1509661486570937692039469)
        ·
          refine ⟨566123057464101634514801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1509661486570937692039469 566123057464101634514801)
          ·
            refine ⟨424592293098076225886101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 566123057464101634514801 424592293098076225886101)
            ·
              refine ⟨19902763738972323088411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 424592293098076225886101 19902763738972323088411)
              ·
                rfl

theorem cell20_392450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_392450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392450 prefixEnd_392450 := by exact prefixLift 392450
  have htrace : WordTrace (prefixWord ++ tailWord_392450) baseStart_392450 baseEnd_392450 := by
    simpa [prefixWord, tailWord_392450, baseEnd_392450] using wordTrace_append hprefix tailTrace_392450
  have hstable : (prefixWord ++ tailWord_392450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392450).length < 2 ^ (prefixWord ++ tailWord_392450).sum := by decide
  have hdescent : baseEnd_392450 < baseStart_392450 := by decide
  rcases family_descends (prefixWord ++ tailWord_392450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392474 : List Nat := [3, 1, 1, 3, 3, 3, 2, 1, 3]
def baseStart_392474 : Nat := 118140960795 + 392474 * 2 ^ 59
def prefixEnd_392474 : Nat := 4983230072969 + 3 ^ 40 * 392474 * 2
def baseEnd_392474 : Nat := 179135827904713490995601

theorem tailTrace_392474 : CollatzResearch.WordTrace tailWord_392474 prefixEnd_392474 179135827904713490995601 := by
  unfold tailWord_392474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3578675695035300516960119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9543135186760801378560317 3578675695035300516960119)
  ·
    refine ⟨5368013542552950775440179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3578675695035300516960119 5368013542552950775440179)
    ·
      refine ⟨8052020313829426163160269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5368013542552950775440179 8052020313829426163160269)
      ·
        refine ⟨3019507617686034811185101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8052020313829426163160269 3019507617686034811185101)
        ·
          refine ⟨1132315356632263054194413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3019507617686034811185101 1132315356632263054194413)
          ·
            refine ⟨424618258737098645322905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1132315356632263054194413 424618258737098645322905)
            ·
              refine ⟨318463694052823983992179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 424618258737098645322905 318463694052823983992179)
              ·
                refine ⟨477695541079235975988269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318463694052823983992179 477695541079235975988269)
                ·
                  refine ⟨179135827904713490995601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 477695541079235975988269 179135827904713490995601)
                  ·
                    rfl

theorem cell20_392474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 2, 1, 3].length) (baseStart_392474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392474 prefixEnd_392474 := by exact prefixLift 392474
  have htrace : WordTrace (prefixWord ++ tailWord_392474) baseStart_392474 baseEnd_392474 := by
    simpa [prefixWord, tailWord_392474, baseEnd_392474] using wordTrace_append hprefix tailTrace_392474
  have hstable : (prefixWord ++ tailWord_392474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392474).length < 2 ^ (prefixWord ++ tailWord_392474).sum := by decide
  have hdescent : baseEnd_392474 < baseStart_392474 := by decide
  rcases family_descends (prefixWord ++ tailWord_392474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392509 : List Nat := [1, 4, 1, 5, 1, 8]
def baseStart_392509 : Nat := 118140960795 + 392509 * 2 ^ 59
def prefixEnd_392509 : Nat := 4983230072969 + 3 ^ 40 * 392509 * 2
def baseEnd_392509 : Nat := 6635251957718849067733

theorem tailTrace_392509 : CollatzResearch.WordTrace tailWord_392509 prefixEnd_392509 6635251957718849067733 := by
  unfold tailWord_392509
  simp only [CollatzResearch.WordTrace]
  refine ⟨14315979335014403045364581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9543986223342935363576387 14315979335014403045364581)
  ·
    refine ⟨2684246125315200571005859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14315979335014403045364581 2684246125315200571005859)
    ·
      refine ⟨4026369187972800856508789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2684246125315200571005859 4026369187972800856508789)
      ·
        refine ⟨377472111372450080297699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4026369187972800856508789 377472111372450080297699)
        ·
          refine ⟨566208167058675120446549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377472111372450080297699 566208167058675120446549)
          ·
            refine ⟨6635251957718849067733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 566208167058675120446549 6635251957718849067733)
            ·
              rfl

theorem cell20_392509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 8].length) (baseStart_392509 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392509 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392509 prefixEnd_392509 := by exact prefixLift 392509
  have htrace : WordTrace (prefixWord ++ tailWord_392509) baseStart_392509 baseEnd_392509 := by
    simpa [prefixWord, tailWord_392509, baseEnd_392509] using wordTrace_append hprefix tailTrace_392509
  have hstable : (prefixWord ++ tailWord_392509).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392509).length < 2 ^ (prefixWord ++ tailWord_392509).sum := by decide
  have hdescent : baseEnd_392509 < baseStart_392509 := by decide
  rcases family_descends (prefixWord ++ tailWord_392509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392519 : List Nat := [1, 1, 4, 1, 2, 3, 4, 2, 2]
def baseStart_392519 : Nat := 118140960795 + 392519 * 2 ^ 59
def prefixEnd_392519 : Nat := 4983230072969 + 3 ^ 40 * 392519 * 2
def baseEnd_392519 : Nat := 179156367130893334495417

theorem tailTrace_392519 : CollatzResearch.WordTrace tailWord_392519 prefixEnd_392519 179156367130893334495417 := by
  unfold tailWord_392519
  simp only [CollatzResearch.WordTrace]
  refine ⟨14316344064978174753228611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9544229376652116502152407 14316344064978174753228611)
  ·
    refine ⟨21474516097467262129842917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14316344064978174753228611 21474516097467262129842917)
    ·
      refine ⟨4026471768275111649345547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21474516097467262129842917 4026471768275111649345547)
      ·
        refine ⟨6039707652412667474018321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4026471768275111649345547 6039707652412667474018321)
        ·
          refine ⟨4529780739309500605513741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6039707652412667474018321 4529780739309500605513741)
          ·
            refine ⟨1698667777241062727067653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4529780739309500605513741 1698667777241062727067653)
            ·
              refine ⟨318500208232699261325185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1698667777241062727067653 318500208232699261325185)
              ·
                refine ⟨238875156174524445993889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 318500208232699261325185 238875156174524445993889)
                ·
                  refine ⟨179156367130893334495417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238875156174524445993889 179156367130893334495417)
                  ·
                    rfl

theorem cell20_392519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 4, 2, 2].length) (baseStart_392519 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392519 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392519 prefixEnd_392519 := by exact prefixLift 392519
  have htrace : WordTrace (prefixWord ++ tailWord_392519) baseStart_392519 baseEnd_392519 := by
    simpa [prefixWord, tailWord_392519, baseEnd_392519] using wordTrace_append hprefix tailTrace_392519
  have hstable : (prefixWord ++ tailWord_392519).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392519).length < 2 ^ (prefixWord ++ tailWord_392519).sum := by decide
  have hdescent : baseEnd_392519 < baseStart_392519 := by decide
  rcases family_descends (prefixWord ++ tailWord_392519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392547 : List Nat := [1, 1, 1, 5, 2, 3, 3, 4]
def baseStart_392547 : Nat := 118140960795 + 392547 * 2 ^ 59
def prefixEnd_392547 : Nat := 4983230072969 + 3 ^ 40 * 392547 * 2
def baseEnd_392547 : Nat := 59723049031283227187323

theorem tailTrace_392547 : CollatzResearch.WordTrace tailWord_392547 prefixEnd_392547 59723049031283227187323 := by
  unfold tailWord_392547
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317365308876735535247895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9544910205917823690165263 14317365308876735535247895)
  ·
    refine ⟨21476047963315103302871843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14317365308876735535247895 21476047963315103302871843)
    ·
      refine ⟨32214071944972654954307765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21476047963315103302871843 32214071944972654954307765)
      ·
        refine ⟨3020069244841186401966353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32214071944972654954307765 3020069244841186401966353)
        ·
          refine ⟨2265051933630889801474765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3020069244841186401966353 2265051933630889801474765)
          ·
            refine ⟨849394475111583675553037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2265051933630889801474765 849394475111583675553037)
            ·
              refine ⟨318522928166843878332389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849394475111583675553037 318522928166843878332389)
              ·
                refine ⟨59723049031283227187323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318522928166843878332389 59723049031283227187323)
                ·
                  rfl

theorem cell20_392547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 3, 4].length) (baseStart_392547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392547 prefixEnd_392547 := by exact prefixLift 392547
  have htrace : WordTrace (prefixWord ++ tailWord_392547) baseStart_392547 baseEnd_392547 := by
    simpa [prefixWord, tailWord_392547, baseEnd_392547] using wordTrace_append hprefix tailTrace_392547
  have hstable : (prefixWord ++ tailWord_392547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392547).length < 2 ^ (prefixWord ++ tailWord_392547).sum := by decide
  have hdescent : baseEnd_392547 < baseStart_392547 := by decide
  rcases family_descends (prefixWord ++ tailWord_392547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392557 : List Nat := [1, 5, 1, 1, 1, 4, 2, 3, 2]
def baseStart_392557 : Nat := 118140960795 + 392557 * 2 ^ 59
def prefixEnd_392557 : Nat := 4983230072969 + 3 ^ 40 * 392557 * 2
def baseEnd_392557 : Nat := 179173711366334091228595

theorem tailTrace_392557 : CollatzResearch.WordTrace tailWord_392557 prefixEnd_392557 179173711366334091228595 := by
  unfold tailWord_392557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14317730038840507243111925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9545153359227004828741283 14317730038840507243111925)
  ·
    refine ⟨1342287191141297554041743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14317730038840507243111925 1342287191141297554041743)
    ·
      refine ⟨2013430786711946331062615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1342287191141297554041743 2013430786711946331062615)
      ·
        refine ⟨3020146180067919496593923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2013430786711946331062615 3020146180067919496593923)
        ·
          refine ⟨4530219270101879244890885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3020146180067919496593923 4530219270101879244890885)
          ·
            refine ⟨849416113144102358417041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4530219270101879244890885 849416113144102358417041)
            ·
              refine ⟨637062084858076768812781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849416113144102358417041 637062084858076768812781)
              ·
                refine ⟨238898281821778788304793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637062084858076768812781 238898281821778788304793)
                ·
                  refine ⟨179173711366334091228595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 238898281821778788304793 179173711366334091228595)
                  ·
                    rfl

theorem cell20_392557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 3, 2].length) (baseStart_392557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392557 prefixEnd_392557 := by exact prefixLift 392557
  have htrace : WordTrace (prefixWord ++ tailWord_392557) baseStart_392557 baseEnd_392557 := by
    simpa [prefixWord, tailWord_392557, baseEnd_392557] using wordTrace_append hprefix tailTrace_392557
  have hstable : (prefixWord ++ tailWord_392557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392557).length < 2 ^ (prefixWord ++ tailWord_392557).sum := by decide
  have hdescent : baseEnd_392557 < baseStart_392557 := by decide
  rcases family_descends (prefixWord ++ tailWord_392557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392574 : List Nat := [4, 2, 3, 2, 1, 1, 2, 1, 4]
def baseStart_392574 : Nat := 118140960795 + 392574 * 2 ^ 59
def prefixEnd_392574 : Nat := 4983230072969 + 3 ^ 40 * 392574 * 2
def baseEnd_392574 : Nat := 179181470629557587661859

theorem tailTrace_392574 : CollatzResearch.WordTrace tailWord_392574 prefixEnd_392574 179181470629557587661859 := by
  unfold tailWord_392574
  simp only [CollatzResearch.WordTrace]
  refine ⟨1789793759972364893310097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9545566719852612764320517 1789793759972364893310097)
  ·
    refine ⟨1342345319979273669982573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1789793759972364893310097 1342345319979273669982573)
    ·
      refine ⟨503379494992227626243465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1342345319979273669982573 503379494992227626243465)
      ·
        refine ⟨377534621244170719682599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 503379494992227626243465 377534621244170719682599)
        ·
          refine ⟨566301931866256079523899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 377534621244170719682599 566301931866256079523899)
          ·
            refine ⟨849452897799384119285849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566301931866256079523899 849452897799384119285849)
            ·
              refine ⟨637089673349538089464387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849452897799384119285849 637089673349538089464387)
              ·
                refine ⟨955634510024307134196581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637089673349538089464387 955634510024307134196581)
                ·
                  refine ⟨179181470629557587661859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955634510024307134196581 179181470629557587661859)
                  ·
                    rfl

theorem cell20_392574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_392574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392574 prefixEnd_392574 := by exact prefixLift 392574
  have htrace : WordTrace (prefixWord ++ tailWord_392574) baseStart_392574 baseEnd_392574 := by
    simpa [prefixWord, tailWord_392574, baseEnd_392574] using wordTrace_append hprefix tailTrace_392574
  have hstable : (prefixWord ++ tailWord_392574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392574).length < 2 ^ (prefixWord ++ tailWord_392574).sum := by decide
  have hdescent : baseEnd_392574 < baseStart_392574 := by decide
  rcases family_descends (prefixWord ++ tailWord_392574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392620 : List Nat := [2, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_392620 : Nat := 118140960795 + 392620 * 2 ^ 59
def prefixEnd_392620 : Nat := 4983230072969 + 3 ^ 40 * 392620 * 2
def baseEnd_392620 : Nat := 179202466282985872128337

theorem tailTrace_392620 : CollatzResearch.WordTrace tailWord_392620 prefixEnd_392620 179202466282985872128337 := by
  unfold tailWord_392620
  simp only [CollatzResearch.WordTrace]
  refine ⟨7160013918806134501327657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9546685225074846001770209 7160013918806134501327657)
  ·
    refine ⟨5370010439104600875995743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7160013918806134501327657 5370010439104600875995743)
    ·
      refine ⟨8055015658656901313993615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5370010439104600875995743 8055015658656901313993615)
      ·
        refine ⟨12082523487985351970990423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8055015658656901313993615 12082523487985351970990423)
        ·
          refine ⟨18123785231978027956485635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12082523487985351970990423 18123785231978027956485635)
          ·
            refine ⟨27185677847967041934728453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18123785231978027956485635 27185677847967041934728453)
            ·
              refine ⟨5097314596493820362761585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27185677847967041934728453 5097314596493820362761585)
              ·
                refine ⟨3822985947370365272071189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5097314596493820362761585 3822985947370365272071189)
                ·
                  refine ⟨179202466282985872128337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3822985947370365272071189 179202466282985872128337)
                  ·
                    rfl

theorem cell20_392620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_392620 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392620 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392620 prefixEnd_392620 := by exact prefixLift 392620
  have htrace : WordTrace (prefixWord ++ tailWord_392620) baseStart_392620 baseEnd_392620 := by
    simpa [prefixWord, tailWord_392620, baseEnd_392620] using wordTrace_append hprefix tailTrace_392620
  have hstable : (prefixWord ++ tailWord_392620).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392620).length < 2 ^ (prefixWord ++ tailWord_392620).sum := by decide
  have hdescent : baseEnd_392620 < baseStart_392620 := by decide
  rcases family_descends (prefixWord ++ tailWord_392620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392633 : List Nat := [1, 2, 1, 4, 5, 1, 1, 1, 4]
def baseStart_392633 : Nat := 118140960795 + 392633 * 2 ^ 59
def prefixEnd_392633 : Nat := 4983230072969 + 3 ^ 40 * 392633 * 2
def baseEnd_392633 : Nat := 179208399837215604694951

theorem tailTrace_392633 : CollatzResearch.WordTrace tailWord_392633 prefixEnd_392633 179208399837215604694951 := by
  unfold tailWord_392633
  simp only [CollatzResearch.WordTrace]
  refine ⟨14320501986565172222878553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9547001324376781481919035 14320501986565172222878553)
  ·
    refine ⟨10740376489923879167158915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14320501986565172222878553 10740376489923879167158915)
    ·
      refine ⟨16110564734885818750738373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10740376489923879167158915 16110564734885818750738373)
      ·
        refine ⟨3020730887791091015763445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16110564734885818750738373 3020730887791091015763445)
        ·
          refine ⟨283193520730414782727823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3020730887791091015763445 283193520730414782727823)
          ·
            refine ⟨424790281095622174091735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283193520730414782727823 424790281095622174091735)
            ·
              refine ⟨637185421643433261137603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424790281095622174091735 637185421643433261137603)
              ·
                refine ⟨955778132465149891706405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 637185421643433261137603 955778132465149891706405)
                ·
                  refine ⟨179208399837215604694951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 955778132465149891706405 179208399837215604694951)
                  ·
                    rfl

theorem cell20_392633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 1, 4].length) (baseStart_392633 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392633 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392633 prefixEnd_392633 := by exact prefixLift 392633
  have htrace : WordTrace (prefixWord ++ tailWord_392633) baseStart_392633 baseEnd_392633 := by
    simpa [prefixWord, tailWord_392633, baseEnd_392633] using wordTrace_append hprefix tailTrace_392633
  have hstable : (prefixWord ++ tailWord_392633).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392633).length < 2 ^ (prefixWord ++ tailWord_392633).sum := by decide
  have hdescent : baseEnd_392633 < baseStart_392633 := by decide
  rcases family_descends (prefixWord ++ tailWord_392633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392682 : List Nat := [3, 1, 3, 1, 4, 8]
def baseStart_392682 : Nat := 118140960795 + 392682 * 2 ^ 59
def prefixEnd_392682 : Nat := 4983230072969 + 3 ^ 40 * 392682 * 2
def baseEnd_392682 : Nat := 6638176473051452298571

theorem tailTrace_392682 : CollatzResearch.WordTrace tailWord_392682 prefixEnd_392682 6638176473051452298571 := by
  unfold tailWord_392682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3580572290846913397853075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9548192775591769060941533 3580572290846913397853075)
  ·
    refine ⟨5370858436270370096779613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3580572290846913397853075 5370858436270370096779613)
    ·
      refine ⟨2014071913601388786292355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5370858436270370096779613 2014071913601388786292355)
      ·
        refine ⟨3021107870402083179438533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014071913601388786292355 3021107870402083179438533)
        ·
          refine ⟨566457725700390596144725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3021107870402083179438533 566457725700390596144725)
          ·
            refine ⟨6638176473051452298571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 566457725700390596144725 6638176473051452298571)
            ·
              rfl

theorem cell20_392682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 8].length) (baseStart_392682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392682 prefixEnd_392682 := by exact prefixLift 392682
  have htrace : WordTrace (prefixWord ++ tailWord_392682) baseStart_392682 baseEnd_392682 := by
    simpa [prefixWord, tailWord_392682, baseEnd_392682] using wordTrace_append hprefix tailTrace_392682
  have hstable : (prefixWord ++ tailWord_392682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392682).length < 2 ^ (prefixWord ++ tailWord_392682).sum := by decide
  have hdescent : baseEnd_392682 < baseStart_392682 := by decide
  rcases family_descends (prefixWord ++ tailWord_392682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392703 : List Nat := [1, 1, 2, 2, 1, 2, 2, 9]
def baseStart_392703 : Nat := 118140960795 + 392703 * 2 ^ 59
def prefixEnd_392703 : Nat := 4983230072969 + 3 ^ 40 * 392703 * 2
def baseEnd_392703 : Nat := 59746783248202157453777

theorem tailTrace_392703 : CollatzResearch.WordTrace tailWord_392703 prefixEnd_392703 59746783248202157453777 := by
  unfold tailWord_392703
  simp only [CollatzResearch.WordTrace]
  refine ⟨14323055096311574177926763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9548703397541049451951175 14323055096311574177926763)
  ·
    refine ⟨21484582644467361266890145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14323055096311574177926763 21484582644467361266890145)
    ·
      refine ⟨16113436983350520950167609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21484582644467361266890145 16113436983350520950167609)
      ·
        refine ⟨12085077737512890712625707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16113436983350520950167609 12085077737512890712625707)
        ·
          refine ⟨18127616606269336068938561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12085077737512890712625707 18127616606269336068938561)
          ·
            refine ⟨13595712454702002051703921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18127616606269336068938561 13595712454702002051703921)
            ·
              refine ⟨10196784341026501538777941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13595712454702002051703921 10196784341026501538777941)
              ·
                refine ⟨59746783248202157453777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10196784341026501538777941 59746783248202157453777)
                ·
                  rfl

theorem cell20_392703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 9].length) (baseStart_392703 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392703 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392703 prefixEnd_392703 := by exact prefixLift 392703
  have htrace : WordTrace (prefixWord ++ tailWord_392703) baseStart_392703 baseEnd_392703 := by
    simpa [prefixWord, tailWord_392703, baseEnd_392703] using wordTrace_append hprefix tailTrace_392703
  have hstable : (prefixWord ++ tailWord_392703).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392703).length < 2 ^ (prefixWord ++ tailWord_392703).sum := by decide
  have hdescent : baseEnd_392703 < baseStart_392703 := by decide
  rcases family_descends (prefixWord ++ tailWord_392703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392761 : List Nat := [1, 2, 1, 5, 1, 3, 3, 1, 3]
def baseStart_392761 : Nat := 118140960795 + 392761 * 2 ^ 59
def prefixEnd_392761 : Nat := 4983230072969 + 3 ^ 40 * 392761 * 2
def baseEnd_392761 : Nat := 179266822525016048427761

theorem tailTrace_392761 : CollatzResearch.WordTrace tailWord_392761 prefixEnd_392761 179266822525016048427761 := by
  unfold tailWord_392761
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325170530101450083538137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9550113686734300055692091 14325170530101450083538137)
  ·
    refine ⟨10743877897576087562653603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14325170530101450083538137 10743877897576087562653603)
    ·
      refine ⟨16115816846364131343980405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10743877897576087562653603 16115816846364131343980405)
      ·
        refine ⟨1510857829346637313498163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16115816846364131343980405 1510857829346637313498163)
        ·
          refine ⟨2266286744019955970247245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1510857829346637313498163 2266286744019955970247245)
          ·
            refine ⟨849857529007483488842717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2266286744019955970247245 849857529007483488842717)
            ·
              refine ⟨318696573377806308316019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 849857529007483488842717 318696573377806308316019)
              ·
                refine ⟨478044860066709462474029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 318696573377806308316019 478044860066709462474029)
                ·
                  refine ⟨179266822525016048427761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478044860066709462474029 179266822525016048427761)
                  ·
                    rfl

theorem cell20_392761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 3, 1, 3].length) (baseStart_392761 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392761 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392761 prefixEnd_392761 := by exact prefixLift 392761
  have htrace : WordTrace (prefixWord ++ tailWord_392761) baseStart_392761 baseEnd_392761 := by
    simpa [prefixWord, tailWord_392761, baseEnd_392761] using wordTrace_append hprefix tailTrace_392761
  have hstable : (prefixWord ++ tailWord_392761).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392761).length < 2 ^ (prefixWord ++ tailWord_392761).sum := by decide
  have hdescent : baseEnd_392761 < baseStart_392761 := by decide
  rcases family_descends (prefixWord ++ tailWord_392761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392781 : List Nat := [1, 6, 1, 1, 4, 1, 1, 3, 2]
def baseStart_392781 : Nat := 118140960795 + 392781 * 2 ^ 59
def prefixEnd_392781 : Nat := 4983230072969 + 3 ^ 40 * 392781 * 2
def baseEnd_392781 : Nat := 179275951069984867761013

theorem tailTrace_392781 : CollatzResearch.WordTrace tailWord_392781 prefixEnd_392781 179275951069984867761013 := by
  unfold tailWord_392781
  simp only [CollatzResearch.WordTrace]
  refine ⟨14325899990028993499266197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9550599993352662332844131 14325899990028993499266197)
  ·
    refine ⟨671526562032609070278103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14325899990028993499266197 671526562032609070278103)
    ·
      refine ⟨1007289843048913605417155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671526562032609070278103 1007289843048913605417155)
      ·
        refine ⟨1510934764573370408125733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007289843048913605417155 1510934764573370408125733)
        ·
          refine ⟨283300268357506951523575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1510934764573370408125733 283300268357506951523575)
          ·
            refine ⟨424950402536260427285363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283300268357506951523575 424950402536260427285363)
            ·
              refine ⟨637425603804390640928045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 424950402536260427285363 637425603804390640928045)
              ·
                refine ⟨239034601426646490348017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637425603804390640928045 239034601426646490348017)
                ·
                  refine ⟨179275951069984867761013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239034601426646490348017 179275951069984867761013)
                  ·
                    rfl

theorem cell20_392781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2].length) (baseStart_392781 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392781 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392781 prefixEnd_392781 := by exact prefixLift 392781
  have htrace : WordTrace (prefixWord ++ tailWord_392781) baseStart_392781 baseEnd_392781 := by
    simpa [prefixWord, tailWord_392781, baseEnd_392781] using wordTrace_append hprefix tailTrace_392781
  have hstable : (prefixWord ++ tailWord_392781).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392781).length < 2 ^ (prefixWord ++ tailWord_392781).sum := by decide
  have hdescent : baseEnd_392781 < baseStart_392781 := by decide
  rcases family_descends (prefixWord ++ tailWord_392781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392796 : List Nat := [2, 2, 4, 1, 2, 1, 8]
def baseStart_392796 : Nat := 118140960795 + 392796 * 2 ^ 59
def prefixEnd_392796 : Nat := 4983230072969 + 3 ^ 40 * 392796 * 2
def baseEnd_392796 : Nat := 19920310830967942473439

theorem tailTrace_392796 : CollatzResearch.WordTrace tailWord_392796 prefixEnd_392796 19920310830967942473439 := by
  unfold tailWord_392796
  simp only [CollatzResearch.WordTrace]
  refine ⟨7163223542487325530531121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9550964723316434040708161 7163223542487325530531121)
  ·
    refine ⟨5372417656865494147898341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7163223542487325530531121 5372417656865494147898341)
    ·
      refine ⟨1007328310662280152730939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5372417656865494147898341 1007328310662280152730939)
      ·
        refine ⟨1510992465993420229096409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1007328310662280152730939 1510992465993420229096409)
        ·
          refine ⟨1133244349495065171822307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1510992465993420229096409 1133244349495065171822307)
          ·
            refine ⟨1699866524242597757733461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1133244349495065171822307 1699866524242597757733461)
            ·
              refine ⟨19920310830967942473439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1699866524242597757733461 19920310830967942473439)
              ·
                rfl

theorem cell20_392796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 8].length) (baseStart_392796 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392796 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392796 prefixEnd_392796 := by exact prefixLift 392796
  have htrace : WordTrace (prefixWord ++ tailWord_392796) baseStart_392796 baseEnd_392796 := by
    simpa [prefixWord, tailWord_392796, baseEnd_392796] using wordTrace_append hprefix tailTrace_392796
  have hstable : (prefixWord ++ tailWord_392796).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392796).length < 2 ^ (prefixWord ++ tailWord_392796).sum := by decide
  have hdescent : baseEnd_392796 < baseStart_392796 := by decide
  rcases family_descends (prefixWord ++ tailWord_392796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392803 : List Nat := [1, 1, 1, 5, 1, 3, 2, 1, 5]
def baseStart_392803 : Nat := 118140960795 + 392803 * 2 ^ 59
def prefixEnd_392803 : Nat := 4983230072969 + 3 ^ 40 * 392803 * 2
def baseEnd_392803 : Nat := 179285992469450569027589

theorem tailTrace_392803 : CollatzResearch.WordTrace tailWord_392803 prefixEnd_392803 179285992469450569027589 := by
  unfold tailWord_392803
  simp only [CollatzResearch.WordTrace]
  refine ⟨14326702395949291256567063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9551134930632860837711375 14326702395949291256567063)
  ·
    refine ⟨21490053593923936884850595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14326702395949291256567063 21490053593923936884850595)
    ·
      refine ⟨32235080390885905327275893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21490053593923936884850595 32235080390885905327275893)
      ·
        refine ⟨3022038786645553624432115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 32235080390885905327275893 3022038786645553624432115)
        ·
          refine ⟨4533058179968330436648173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3022038786645553624432115 4533058179968330436648173)
          ·
            refine ⟨1699896817488123913743065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4533058179968330436648173 1699896817488123913743065)
            ·
              refine ⟨1274922613116092935307299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1699896817488123913743065 1274922613116092935307299)
              ·
                refine ⟨1912383919674139402960949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1274922613116092935307299 1912383919674139402960949)
                ·
                  refine ⟨179285992469450569027589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1912383919674139402960949 179285992469450569027589)
                  ·
                    rfl

theorem cell20_392803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 2, 1, 5].length) (baseStart_392803 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392803 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392803 prefixEnd_392803 := by exact prefixLift 392803
  have htrace : WordTrace (prefixWord ++ tailWord_392803) baseStart_392803 baseEnd_392803 := by
    simpa [prefixWord, tailWord_392803, baseEnd_392803] using wordTrace_append hprefix tailTrace_392803
  have hstable : (prefixWord ++ tailWord_392803).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392803).length < 2 ^ (prefixWord ++ tailWord_392803).sum := by decide
  have hdescent : baseEnd_392803 < baseStart_392803 := by decide
  rcases family_descends (prefixWord ++ tailWord_392803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392813 : List Nat := [1, 5, 1, 1, 4, 1, 2, 5]
def baseStart_392813 : Nat := 118140960795 + 392813 * 2 ^ 59
def prefixEnd_392813 : Nat := 4983230072969 + 3 ^ 40 * 392813 * 2
def baseEnd_392813 : Nat := 59763518913978326231405

theorem tailTrace_392813 : CollatzResearch.WordTrace tailWord_392813 prefixEnd_392813 59763518913978326231405 := by
  unfold tailWord_392813
  simp only [CollatzResearch.WordTrace]
  refine ⟨14327067125913062964431093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9551378083942041976287395 14327067125913062964431093)
  ·
    refine ⟨1343162543054349652915415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14327067125913062964431093 1343162543054349652915415)
    ·
      refine ⟨2014743814581524479373123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343162543054349652915415 2014743814581524479373123)
      ·
        refine ⟨3022115721872286719059685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2014743814581524479373123 3022115721872286719059685)
        ·
          refine ⟨566646697851053759823691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3022115721872286719059685 566646697851053759823691)
          ·
            refine ⟨849970046776580639735537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 566646697851053759823691 849970046776580639735537)
            ·
              refine ⟨637477535082435479801653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 849970046776580639735537 637477535082435479801653)
              ·
                refine ⟨59763518913978326231405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 637477535082435479801653 59763518913978326231405)
                ·
                  rfl

theorem cell20_392813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 4, 1, 2, 5].length) (baseStart_392813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392813 prefixEnd_392813 := by exact prefixLift 392813
  have htrace : WordTrace (prefixWord ++ tailWord_392813) baseStart_392813 baseEnd_392813 := by
    simpa [prefixWord, tailWord_392813, baseEnd_392813] using wordTrace_append hprefix tailTrace_392813
  have hstable : (prefixWord ++ tailWord_392813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392813).length < 2 ^ (prefixWord ++ tailWord_392813).sum := by decide
  have hdescent : baseEnd_392813 < baseStart_392813 := by decide
  rcases family_descends (prefixWord ++ tailWord_392813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392855 : List Nat := [1, 1, 3, 3, 2, 10]
def baseStart_392855 : Nat := 118140960795 + 392855 * 2 ^ 59
def prefixEnd_392855 : Nat := 4983230072969 + 3 ^ 40 * 392855 * 2
def baseEnd_392855 : Nat := 6641100988384055529409

theorem tailTrace_392855 : CollatzResearch.WordTrace tailWord_392855 prefixEnd_392855 6641100988384055529409 := by
  unfold tailWord_392855
  simp only [CollatzResearch.WordTrace]
  refine ⟨14328598991760904137460019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9552399327840602758306679 14328598991760904137460019)
  ·
    refine ⟨21492898487641356206190029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14328598991760904137460019 21492898487641356206190029)
    ·
      refine ⟨8059836932865508577321261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21492898487641356206190029 8059836932865508577321261)
      ·
        refine ⟨3022438849824565716495473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8059836932865508577321261 3022438849824565716495473)
        ·
          refine ⟨2266829137368424287371605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3022438849824565716495473 2266829137368424287371605)
          ·
            refine ⟨6641100988384055529409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 2266829137368424287371605 6641100988384055529409)
            ·
              rfl

theorem cell20_392855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 10].length) (baseStart_392855 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392855 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392855 prefixEnd_392855 := by exact prefixLift 392855
  have htrace : WordTrace (prefixWord ++ tailWord_392855) baseStart_392855 baseEnd_392855 := by
    simpa [prefixWord, tailWord_392855, baseEnd_392855] using wordTrace_append hprefix tailTrace_392855
  have hstable : (prefixWord ++ tailWord_392855).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392855).length < 2 ^ (prefixWord ++ tailWord_392855).sum := by decide
  have hdescent : baseEnd_392855 < baseStart_392855 := by decide
  rcases family_descends (prefixWord ++ tailWord_392855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392879 : List Nat := [1, 1, 2, 1, 2, 4, 1, 5, 3]
def baseStart_392879 : Nat := 118140960795 + 392879 * 2 ^ 59
def prefixEnd_392879 : Nat := 4983230072969 + 3 ^ 40 * 392879 * 2
def baseEnd_392879 : Nat := 179320680940332082493945

theorem tailTrace_392879 : CollatzResearch.WordTrace tailWord_392879 prefixEnd_392879 179320680940332082493945 := by
  unfold tailWord_392879
  simp only [CollatzResearch.WordTrace]
  refine ⟨14329474343673956236333691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9552982895782637490889127 14329474343673956236333691)
  ·
    refine ⟨21494211515510934354500537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14329474343673956236333691 21494211515510934354500537)
    ·
      refine ⟨16120658636633200765875403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21494211515510934354500537 16120658636633200765875403)
      ·
        refine ⟨24180987954949801148813105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16120658636633200765875403 24180987954949801148813105)
        ·
          refine ⟨18135740966212350861609829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24180987954949801148813105 18135740966212350861609829)
          ·
            refine ⟨3400451431164815786551843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 18135740966212350861609829 3400451431164815786551843)
            ·
              refine ⟨5100677146747223679827765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3400451431164815786551843 5100677146747223679827765)
              ·
                refine ⟨478188482507552219983853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5100677146747223679827765 478188482507552219983853)
                ·
                  refine ⟨179320680940332082493945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478188482507552219983853 179320680940332082493945)
                  ·
                    rfl

theorem cell20_392879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 5, 3].length) (baseStart_392879 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392879 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392879 prefixEnd_392879 := by exact prefixLift 392879
  have htrace : WordTrace (prefixWord ++ tailWord_392879) baseStart_392879 baseEnd_392879 := by
    simpa [prefixWord, tailWord_392879, baseEnd_392879] using wordTrace_append hprefix tailTrace_392879
  have hstable : (prefixWord ++ tailWord_392879).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392879).length < 2 ^ (prefixWord ++ tailWord_392879).sum := by decide
  have hdescent : baseEnd_392879 < baseStart_392879 := by decide
  rcases family_descends (prefixWord ++ tailWord_392879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392941 : List Nat := [1, 5, 1, 2, 1, 2, 2, 2, 4]
def baseStart_392941 : Nat := 118140960795 + 392941 * 2 ^ 59
def prefixEnd_392941 : Nat := 4983230072969 + 3 ^ 40 * 392941 * 2
def baseEnd_392941 : Nat := 179348979429735422427025

theorem tailTrace_392941 : CollatzResearch.WordTrace tailWord_392941 prefixEnd_392941 179348979429735422427025 := by
  unfold tailWord_392941
  simp only [CollatzResearch.WordTrace]
  refine ⟨14331735669449340825090677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9554490446299560550060451 14331735669449340825090677)
  ·
    refine ⟨1343600219010875702352251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14331735669449340825090677 1343600219010875702352251)
    ·
      refine ⟨2015400328516313553528377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1343600219010875702352251 2015400328516313553528377)
      ·
        refine ⟨1511550246387235165146283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2015400328516313553528377 1511550246387235165146283)
        ·
          refine ⟨2267325369580852747719425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1511550246387235165146283 2267325369580852747719425)
          ·
            refine ⟨1700494027185639560789569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2267325369580852747719425 1700494027185639560789569)
            ·
              refine ⟨1275370520389229670592177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1700494027185639560789569 1275370520389229670592177)
              ·
                refine ⟨956527890291922252944133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1275370520389229670592177 956527890291922252944133)
                ·
                  refine ⟨179348979429735422427025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 956527890291922252944133 179348979429735422427025)
                  ·
                    rfl

theorem cell20_392941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_392941 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392941 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392941 prefixEnd_392941 := by exact prefixLift 392941
  have htrace : WordTrace (prefixWord ++ tailWord_392941) baseStart_392941 baseEnd_392941 := by
    simpa [prefixWord, tailWord_392941, baseEnd_392941] using wordTrace_append hprefix tailTrace_392941
  have hstable : (prefixWord ++ tailWord_392941).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392941).length < 2 ^ (prefixWord ++ tailWord_392941).sum := by decide
  have hdescent : baseEnd_392941 < baseStart_392941 := by decide
  rcases family_descends (prefixWord ++ tailWord_392941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_392986 : List Nat := [3, 1, 1, 3, 2, 3, 2, 5]
def baseStart_392986 : Nat := 118140960795 + 392986 * 2 ^ 59
def prefixEnd_392986 : Nat := 4983230072969 + 3 ^ 40 * 392986 * 2
def baseEnd_392986 : Nat := 59789839551971755308947

theorem tailTrace_392986 : CollatzResearch.WordTrace tailWord_392986 prefixEnd_392986 59789839551971755308947 := by
  unfold tailWord_392986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3583344238571578377619703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9555584636190875673652541 3583344238571578377619703)
  ·
    refine ⟨5375016357857367566429555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3583344238571578377619703 5375016357857367566429555)
    ·
      refine ⟨8062524536786051349644333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5375016357857367566429555 8062524536786051349644333)
      ·
        refine ⟨3023446701294769256116625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8062524536786051349644333 3023446701294769256116625)
        ·
          refine ⟨2267585025971076942087469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3023446701294769256116625 2267585025971076942087469)
          ·
            refine ⟨850344384739153853282801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2267585025971076942087469 850344384739153853282801)
            ·
              refine ⟨637758288554365389962101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 850344384739153853282801 637758288554365389962101)
              ·
                refine ⟨59789839551971755308947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 637758288554365389962101 59789839551971755308947)
                ·
                  rfl

theorem cell20_392986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_392986 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_392986 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_392986 prefixEnd_392986 := by exact prefixLift 392986
  have htrace : WordTrace (prefixWord ++ tailWord_392986) baseStart_392986 baseEnd_392986 := by
    simpa [prefixWord, tailWord_392986, baseEnd_392986] using wordTrace_append hprefix tailTrace_392986
  have hstable : (prefixWord ++ tailWord_392986).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_392986).length < 2 ^ (prefixWord ++ tailWord_392986).sum := by decide
  have hdescent : baseEnd_392986 < baseStart_392986 := by decide
  rcases family_descends (prefixWord ++ tailWord_392986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393030 : List Nat := [6, 1, 1, 2, 1, 2, 1, 4, 2]
def baseStart_393030 : Nat := 118140960795 + 393030 * 2 ^ 59
def prefixEnd_393030 : Nat := 4983230072969 + 3 ^ 40 * 393030 * 2
def baseEnd_393030 : Nat := 179389601454846668459995

theorem tailTrace_393030 : CollatzResearch.WordTrace tailWord_393030 prefixEnd_393030 179389601454846668459995 := by
  unfold tailWord_393030
  simp only [CollatzResearch.WordTrace]
  refine ⟨447968180191465907033767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 9556654510751272683387029 447968180191465907033767)
  ·
    refine ⟨671952270287198860550651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 447968180191465907033767 671952270287198860550651)
    ·
      refine ⟨1007928405430798290825977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 671952270287198860550651 1007928405430798290825977)
      ·
        refine ⟨755946304073098718119483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1007928405430798290825977 755946304073098718119483)
        ·
          refine ⟨1133919456109648077179225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 755946304073098718119483 1133919456109648077179225)
          ·
            refine ⟨850439592082236057884419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1133919456109648077179225 850439592082236057884419)
            ·
              refine ⟨1275659388123354086826629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 850439592082236057884419 1275659388123354086826629)
              ·
                refine ⟨239186135273128891279993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1275659388123354086826629 239186135273128891279993)
                ·
                  refine ⟨179389601454846668459995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239186135273128891279993 179389601454846668459995)
                  ·
                    rfl

theorem cell20_393030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2].length) (baseStart_393030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393030 prefixEnd_393030 := by exact prefixLift 393030
  have htrace : WordTrace (prefixWord ++ tailWord_393030) baseStart_393030 baseEnd_393030 := by
    simpa [prefixWord, tailWord_393030, baseEnd_393030] using wordTrace_append hprefix tailTrace_393030
  have hstable : (prefixWord ++ tailWord_393030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393030).length < 2 ^ (prefixWord ++ tailWord_393030).sum := by decide
  have hdescent : baseEnd_393030 < baseStart_393030 := by decide
  rcases family_descends (prefixWord ++ tailWord_393030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393031 : List Nat := [1, 1, 4, 1, 2, 1, 3, 4, 3]
def baseStart_393031 : Nat := 118140960795 + 393031 * 2 ^ 59
def prefixEnd_393031 : Nat := 4983230072969 + 3 ^ 40 * 393031 * 2
def baseEnd_393031 : Nat := 179390057882095109426657

theorem tailTrace_393031 : CollatzResearch.WordTrace tailWord_393031 prefixEnd_393031 179390057882095109426657 := by
  unfold tailWord_393031
  simp only [CollatzResearch.WordTrace]
  refine ⟨14335018239123286195866947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9556678826082190797244631 14335018239123286195866947)
  ·
    refine ⟨21502527358684929293800421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14335018239123286195866947 21502527358684929293800421)
    ·
      refine ⟨4031723879753424242587579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21502527358684929293800421 4031723879753424242587579)
      ·
        refine ⟨6047585819630136363881369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4031723879753424242587579 6047585819630136363881369)
        ·
          refine ⟨4535689364722602272911027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6047585819630136363881369 4535689364722602272911027)
          ·
            refine ⟨6803534047083903409366541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4535689364722602272911027 6803534047083903409366541)
            ·
              refine ⟨2551325267656463778512453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6803534047083903409366541 2551325267656463778512453)
              ·
                refine ⟨478373487685586958471085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2551325267656463778512453 478373487685586958471085)
                ·
                  refine ⟨179390057882095109426657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478373487685586958471085 179390057882095109426657)
                  ·
                    rfl

theorem cell20_393031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 4, 3].length) (baseStart_393031 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393031 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393031 prefixEnd_393031 := by exact prefixLift 393031
  have htrace : WordTrace (prefixWord ++ tailWord_393031) baseStart_393031 baseEnd_393031 := by
    simpa [prefixWord, tailWord_393031, baseEnd_393031] using wordTrace_append hprefix tailTrace_393031
  have hstable : (prefixWord ++ tailWord_393031).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393031).length < 2 ^ (prefixWord ++ tailWord_393031).sum := by decide
  have hdescent : baseEnd_393031 < baseStart_393031 := by decide
  rcases family_descends (prefixWord ++ tailWord_393031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393093 : List Nat := [1, 3, 1, 1, 3, 2, 1, 6, 2]
def baseStart_393093 : Nat := 118140960795 + 393093 * 2 ^ 59
def prefixEnd_393093 : Nat := 4983230072969 + 3 ^ 40 * 393093 * 2
def baseEnd_393093 : Nat := 179418356371498449359737

theorem tailTrace_393093 : CollatzResearch.WordTrace tailWord_393093 prefixEnd_393093 179418356371498449359737 := by
  unfold tailWord_393093
  simp only [CollatzResearch.WordTrace]
  refine ⟨14337279564898670784623933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9558186376599113856415955 14337279564898670784623933)
  ·
    refine ⟨5376479836837001544233975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14337279564898670784623933 5376479836837001544233975)
    ·
      refine ⟨8064719755255502316350963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5376479836837001544233975 8064719755255502316350963)
      ·
        refine ⟨12097079632883253474526445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8064719755255502316350963 12097079632883253474526445)
        ·
          refine ⟨4536404862331220052947417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12097079632883253474526445 4536404862331220052947417)
          ·
            refine ⟨3402303646748415039710563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4536404862331220052947417 3402303646748415039710563)
            ·
              refine ⟨5103455470122622559565845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3402303646748415039710563 5103455470122622559565845)
              ·
                refine ⟨239224475161997932479649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5103455470122622559565845 239224475161997932479649)
                ·
                  refine ⟨179418356371498449359737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239224475161997932479649 179418356371498449359737)
                  ·
                    rfl

theorem cell20_393093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 6, 2].length) (baseStart_393093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393093 prefixEnd_393093 := by exact prefixLift 393093
  have htrace : WordTrace (prefixWord ++ tailWord_393093) baseStart_393093 baseEnd_393093 := by
    simpa [prefixWord, tailWord_393093, baseEnd_393093] using wordTrace_append hprefix tailTrace_393093
  have hstable : (prefixWord ++ tailWord_393093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393093).length < 2 ^ (prefixWord ++ tailWord_393093).sum := by decide
  have hdescent : baseEnd_393093 < baseStart_393093 := by decide
  rcases family_descends (prefixWord ++ tailWord_393093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393117 : List Nat := [1, 4, 2, 1, 2, 4, 2, 4]
def baseStart_393117 : Nat := 118140960795 + 393117 * 2 ^ 59
def prefixEnd_393117 : Nat := 4983230072969 + 3 ^ 40 * 393117 * 2
def baseEnd_393117 : Nat := 59809770208487010853213

theorem tailTrace_393117 : CollatzResearch.WordTrace tailWord_393117 prefixEnd_393117 59809770208487010853213 := by
  unfold tailWord_393117
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338154916811722883497605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9558769944541148588998403 14338154916811722883497605)
  ·
    refine ⟨2688404046902198040655801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14338154916811722883497605 2688404046902198040655801)
    ·
      refine ⟨2016303035176648530491851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2688404046902198040655801 2016303035176648530491851)
      ·
        refine ⟨3024454552764972795737777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2016303035176648530491851 3024454552764972795737777)
        ·
          refine ⟨2268340914573729596803333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024454552764972795737777 2268340914573729596803333)
          ·
            refine ⟨425313921482574299400625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2268340914573729596803333 425313921482574299400625)
            ·
              refine ⟨318985441111930724550469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425313921482574299400625 318985441111930724550469)
              ·
                refine ⟨59809770208487010853213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 318985441111930724550469 59809770208487010853213)
                ·
                  rfl

theorem cell20_393117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 4, 2, 4].length) (baseStart_393117 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393117 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393117 prefixEnd_393117 := by exact prefixLift 393117
  have htrace : WordTrace (prefixWord ++ tailWord_393117) baseStart_393117 baseEnd_393117 := by
    simpa [prefixWord, tailWord_393117, baseEnd_393117] using wordTrace_append hprefix tailTrace_393117
  have hstable : (prefixWord ++ tailWord_393117).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393117).length < 2 ^ (prefixWord ++ tailWord_393117).sum := by decide
  have hdescent : baseEnd_393117 < baseStart_393117 := by decide
  rcases family_descends (prefixWord ++ tailWord_393117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393127 : List Nat := [1, 1, 6, 1, 2, 3, 1, 3, 2]
def baseStart_393127 : Nat := 118140960795 + 393127 * 2 ^ 59
def prefixEnd_393127 : Nat := 4983230072969 + 3 ^ 40 * 393127 * 2
def baseEnd_393127 : Nat := 179433874897945442226265

theorem tailTrace_393127 : CollatzResearch.WordTrace tailWord_393127 prefixEnd_393127 179433874897945442226265 := by
  unfold tailWord_393127
  simp only [CollatzResearch.WordTrace]
  refine ⟨14338519646775494591361635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9559013097850329727574423 14338519646775494591361635)
  ·
    refine ⟨21507779470163241887042453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14338519646775494591361635 21507779470163241887042453)
    ·
      refine ⟨1008177162663901963455115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21507779470163241887042453 1008177162663901963455115)
      ·
        refine ⟨1512265743995852945182673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008177162663901963455115 1512265743995852945182673)
        ·
          refine ⟨1134199307996889708887005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1512265743995852945182673 1134199307996889708887005)
          ·
            refine ⟨425324740498833640832627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1134199307996889708887005 425324740498833640832627)
            ·
              refine ⟨637987110748250461248941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425324740498833640832627 637987110748250461248941)
              ·
                refine ⟨239245166530593922968353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 637987110748250461248941 239245166530593922968353)
                ·
                  refine ⟨179433874897945442226265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239245166530593922968353 179433874897945442226265)
                  ·
                    rfl

theorem cell20_393127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 3, 1, 3, 2].length) (baseStart_393127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393127 prefixEnd_393127 := by exact prefixLift 393127
  have htrace : WordTrace (prefixWord ++ tailWord_393127) baseStart_393127 baseEnd_393127 := by
    simpa [prefixWord, tailWord_393127, baseEnd_393127] using wordTrace_append hprefix tailTrace_393127
  have hstable : (prefixWord ++ tailWord_393127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393127).length < 2 ^ (prefixWord ++ tailWord_393127).sum := by decide
  have hdescent : baseEnd_393127 < baseStart_393127 := by decide
  rcases family_descends (prefixWord ++ tailWord_393127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393145 : List Nat := [1, 2, 1, 4, 2, 1, 2, 4, 3]
def baseStart_393145 : Nat := 118140960795 + 393145 * 2 ^ 59
def prefixEnd_393145 : Nat := 4983230072969 + 3 ^ 40 * 393145 * 2
def baseEnd_393145 : Nat := 179442090588417379626191

theorem tailTrace_393145 : CollatzResearch.WordTrace tailWord_393145 prefixEnd_393145 179442090588417379626191 := by
  unfold tailWord_393145
  simp only [CollatzResearch.WordTrace]
  refine ⟨14339176160710283665516889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9559450773806855777011259 14339176160710283665516889)
  ·
    refine ⟨10754382120532712749137667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14339176160710283665516889 10754382120532712749137667)
    ·
      refine ⟨16131573180799069123706501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10754382120532712749137667 16131573180799069123706501)
      ·
        refine ⟨3024669971399825460694969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16131573180799069123706501 3024669971399825460694969)
        ·
          refine ⟨2268502478549869095521227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3024669971399825460694969 2268502478549869095521227)
          ·
            refine ⟨3402753717824803643281841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268502478549869095521227 3402753717824803643281841)
            ·
              refine ⟨2552065288368602732461381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3402753717824803643281841 2552065288368602732461381)
              ·
                refine ⟨478512241569113012336509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2552065288368602732461381 478512241569113012336509)
                ·
                  refine ⟨179442090588417379626191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478512241569113012336509 179442090588417379626191)
                  ·
                    rfl

theorem cell20_393145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 4, 3].length) (baseStart_393145 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393145 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393145 prefixEnd_393145 := by exact prefixLift 393145
  have htrace : WordTrace (prefixWord ++ tailWord_393145) baseStart_393145 baseEnd_393145 := by
    simpa [prefixWord, tailWord_393145, baseEnd_393145] using wordTrace_append hprefix tailTrace_393145
  have hstable : (prefixWord ++ tailWord_393145).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393145).length < 2 ^ (prefixWord ++ tailWord_393145).sum := by decide
  have hdescent : baseEnd_393145 < baseStart_393145 := by decide
  rcases family_descends (prefixWord ++ tailWord_393145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393162 : List Nat := [3, 1, 2, 1, 2, 1, 6, 1, 3]
def baseStart_393162 : Nat := 118140960795 + 393162 * 2 ^ 59
def prefixEnd_393162 : Nat := 4983230072969 + 3 ^ 40 * 393162 * 2
def baseEnd_393162 : Nat := 179449849851640876059455

theorem tailTrace_393162 : CollatzResearch.WordTrace tailWord_393162 prefixEnd_393162 179449849851640876059455 := by
  unfold tailWord_393162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3584949050412173892221435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9559864134432463712590493 3584949050412173892221435)
  ·
    refine ⟨5377423575618260838332153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3584949050412173892221435 5377423575618260838332153)
    ·
      refine ⟨4033067681713695628749115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5377423575618260838332153 4033067681713695628749115)
      ·
        refine ⟨6049601522570543443123673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4033067681713695628749115 6049601522570543443123673)
        ·
          refine ⟨4537201141927907582342755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6049601522570543443123673 4537201141927907582342755)
          ·
            refine ⟨6805801712891861373514133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4537201141927907582342755 6805801712891861373514133)
            ·
              refine ⟨319021955291806001883475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6805801712891861373514133 319021955291806001883475)
              ·
                refine ⟨478532932937709002825213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319021955291806001883475 478532932937709002825213)
                ·
                  refine ⟨179449849851640876059455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478532932937709002825213 179449849851640876059455)
                  ·
                    rfl

theorem cell20_393162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 6, 1, 3].length) (baseStart_393162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393162 prefixEnd_393162 := by exact prefixLift 393162
  have htrace : WordTrace (prefixWord ++ tailWord_393162) baseStart_393162 baseEnd_393162 := by
    simpa [prefixWord, tailWord_393162, baseEnd_393162] using wordTrace_append hprefix tailTrace_393162
  have hstable : (prefixWord ++ tailWord_393162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393162).length < 2 ^ (prefixWord ++ tailWord_393162).sum := by decide
  have hdescent : baseEnd_393162 < baseStart_393162 := by decide
  rcases family_descends (prefixWord ++ tailWord_393162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393221 : List Nat := [1, 3, 1, 1, 2, 4, 2, 3, 3]
def baseStart_393221 : Nat := 118140960795 + 393221 * 2 ^ 59
def prefixEnd_393221 : Nat := 4983230072969 + 3 ^ 40 * 393221 * 2
def baseEnd_393221 : Nat := 179476779059298893092547

theorem tailTrace_393221 : CollatzResearch.WordTrace tailWord_393221 prefixEnd_393221 179476779059298893092547 := by
  unfold tailWord_393221
  simp only [CollatzResearch.WordTrace]
  refine ⟨14341948108434948645283517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9561298738956632430189011 14341948108434948645283517)
  ·
    refine ⟨5378230540663105741981319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14341948108434948645283517 5378230540663105741981319)
    ·
      refine ⟨8067345810994658612971979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378230540663105741981319 8067345810994658612971979)
      ·
        refine ⟨12101018716491987919457969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8067345810994658612971979 12101018716491987919457969)
        ·
          refine ⟨9075764037368990939593477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12101018716491987919457969 9075764037368990939593477)
          ·
            refine ⟨1701705757006685801173777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9075764037368990939593477 1701705757006685801173777)
            ·
              refine ⟨1276279317755014350880333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701705757006685801173777 1276279317755014350880333)
              ·
                refine ⟨478604744158130381580125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1276279317755014350880333 478604744158130381580125)
                ·
                  refine ⟨179476779059298893092547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478604744158130381580125 179476779059298893092547)
                  ·
                    rfl

theorem cell20_393221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 2, 3, 3].length) (baseStart_393221 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393221 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393221 prefixEnd_393221 := by exact prefixLift 393221
  have htrace : WordTrace (prefixWord ++ tailWord_393221) baseStart_393221 baseEnd_393221 := by
    simpa [prefixWord, tailWord_393221, baseEnd_393221] using wordTrace_append hprefix tailTrace_393221
  have hstable : (prefixWord ++ tailWord_393221).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393221).length < 2 ^ (prefixWord ++ tailWord_393221).sum := by decide
  have hdescent : baseEnd_393221 < baseStart_393221 := by decide
  rcases family_descends (prefixWord ++ tailWord_393221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393228 : List Nat := [2, 2, 1, 2, 3, 1, 3, 2, 4]
def baseStart_393228 : Nat := 118140960795 + 393228 * 2 ^ 59
def prefixEnd_393228 : Nat := 4983230072969 + 3 ^ 40 * 393228 * 2
def baseEnd_393228 : Nat := 179479974050037979859185

theorem tailTrace_393228 : CollatzResearch.WordTrace tailWord_393228 prefixEnd_393228 179479974050037979859185 := by
  unfold tailWord_393228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171101709704794420394169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9561468946273059227192225 7171101709704794420394169)
  ·
    refine ⟨5378326282278595815295627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7171101709704794420394169 5378326282278595815295627)
    ·
      refine ⟨8067489423417893722943441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5378326282278595815295627 8067489423417893722943441)
      ·
        refine ⟨6050617067563420292207581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8067489423417893722943441 6050617067563420292207581)
        ·
          refine ⟨2268981400336282609577843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6050617067563420292207581 2268981400336282609577843)
          ·
            refine ⟨3403472100504423914366765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2268981400336282609577843 3403472100504423914366765)
            ·
              refine ⟨1276302037689158967887537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3403472100504423914366765 1276302037689158967887537)
              ·
                refine ⟨957226528266869225915653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1276302037689158967887537 957226528266869225915653)
                ·
                  refine ⟨179479974050037979859185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957226528266869225915653 179479974050037979859185)
                  ·
                    rfl

theorem cell20_393228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 3, 2, 4].length) (baseStart_393228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393228 prefixEnd_393228 := by exact prefixLift 393228
  have htrace : WordTrace (prefixWord ++ tailWord_393228) baseStart_393228 baseEnd_393228 := by
    simpa [prefixWord, tailWord_393228, baseEnd_393228] using wordTrace_append hprefix tailTrace_393228
  have hstable : (prefixWord ++ tailWord_393228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393228).length < 2 ^ (prefixWord ++ tailWord_393228).sum := by decide
  have hdescent : baseEnd_393228 < baseStart_393228 := by decide
  rcases family_descends (prefixWord ++ tailWord_393228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393252 : List Nat := [2, 3, 1, 4, 2, 1, 7]
def baseStart_393252 : Nat := 118140960795 + 393252 * 2 ^ 59
def prefixEnd_393252 : Nat := 4983230072969 + 3 ^ 40 * 393252 * 2
def baseEnd_393252 : Nat := 19943436478222284784343

theorem tailTrace_393252 : CollatzResearch.WordTrace tailWord_393252 prefixEnd_393252 19943436478222284784343 := by
  unfold tailWord_393252
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171539385661320469831005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9562052514215093959774673 7171539385661320469831005)
  ·
    refine ⟨2689327269622995176186627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7171539385661320469831005 2689327269622995176186627)
    ·
      refine ⟨4033990904434492764279941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2689327269622995176186627 4033990904434492764279941)
      ·
        refine ⟨756373294581467393302489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4033990904434492764279941 756373294581467393302489)
        ·
          refine ⟨567279970936100544976867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756373294581467393302489 567279970936100544976867)
          ·
            refine ⟨850919956404150817465301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 567279970936100544976867 850919956404150817465301)
            ·
              refine ⟨19943436478222284784343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 850919956404150817465301 19943436478222284784343)
              ·
                rfl

theorem cell20_393252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 1, 7].length) (baseStart_393252 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393252 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393252 prefixEnd_393252 := by exact prefixLift 393252
  have htrace : WordTrace (prefixWord ++ tailWord_393252) baseStart_393252 baseEnd_393252 := by
    simpa [prefixWord, tailWord_393252, baseEnd_393252] using wordTrace_append hprefix tailTrace_393252
  have hstable : (prefixWord ++ tailWord_393252).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393252).length < 2 ^ (prefixWord ++ tailWord_393252).sum := by decide
  have hdescent : baseEnd_393252 < baseStart_393252 := by decide
  rcases family_descends (prefixWord ++ tailWord_393252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393262 : List Nat := [4, 1, 3, 1, 1, 2, 2, 4, 2]
def baseStart_393262 : Nat := 118140960795 + 393262 * 2 ^ 59
def prefixEnd_393262 : Nat := 4983230072969 + 3 ^ 40 * 393262 * 2
def baseEnd_393262 : Nat := 179495492576484972725713

theorem tailTrace_393262 : CollatzResearch.WordTrace tailWord_393262 prefixEnd_393262 179495492576484972725713 := by
  unfold tailWord_393262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1792930437660801580940755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9562295667524275098350693 1792930437660801580940755)
  ·
    refine ⟨2689395656491202371411133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1792930437660801580940755 2689395656491202371411133)
    ·
      refine ⟨1008523371184200889279175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2689395656491202371411133 1008523371184200889279175)
      ·
        refine ⟨1512785056776301333918763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1008523371184200889279175 1512785056776301333918763)
        ·
          refine ⟨2269177585164452000878145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1512785056776301333918763 2269177585164452000878145)
          ·
            refine ⟨1701883188873339000658609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269177585164452000878145 1701883188873339000658609)
            ·
              refine ⟨1276412391655004250493957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1701883188873339000658609 1276412391655004250493957)
              ·
                refine ⟨239327323435313296967617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1276412391655004250493957 239327323435313296967617)
                ·
                  refine ⟨179495492576484972725713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239327323435313296967617 179495492576484972725713)
                  ·
                    rfl

theorem cell20_393262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 4, 2].length) (baseStart_393262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393262 prefixEnd_393262 := by exact prefixLift 393262
  have htrace : WordTrace (prefixWord ++ tailWord_393262) baseStart_393262 baseEnd_393262 := by
    simpa [prefixWord, tailWord_393262, baseEnd_393262] using wordTrace_append hprefix tailTrace_393262
  have hstable : (prefixWord ++ tailWord_393262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393262).length < 2 ^ (prefixWord ++ tailWord_393262).sum := by decide
  have hdescent : baseEnd_393262 < baseStart_393262 := by decide
  rcases family_descends (prefixWord ++ tailWord_393262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393266 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 4]
def baseStart_393266 : Nat := 118140960795 + 393266 * 2 ^ 59
def prefixEnd_393266 : Nat := 4983230072969 + 3 ^ 40 * 393266 * 2
def baseEnd_393266 : Nat := 179497318285478736592363

theorem tailTrace_393266 : CollatzResearch.WordTrace tailWord_393266 prefixEnd_393266 179497318285478736592363 := by
  unfold tailWord_393266
  simp only [CollatzResearch.WordTrace]
  refine ⟨3585897348317980332667913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9562392928847947553781101 3585897348317980332667913)
  ·
    refine ⟨2689423011238485249500935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3585897348317980332667913 2689423011238485249500935)
    ·
      refine ⟨4034134516857727874251403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2689423011238485249500935 4034134516857727874251403)
      ·
        refine ⟨6051201775286591811377105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4034134516857727874251403 6051201775286591811377105)
        ·
          refine ⟨4538401331464943858532829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6051201775286591811377105 4538401331464943858532829)
          ·
            refine ⟨1701900499299353946949811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4538401331464943858532829 1701900499299353946949811)
            ·
              refine ⟨2552850748949030920424717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1701900499299353946949811 2552850748949030920424717)
              ·
                refine ⟨957319030855886595159269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2552850748949030920424717 957319030855886595159269)
                ·
                  refine ⟨179497318285478736592363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 957319030855886595159269 179497318285478736592363)
                  ·
                    rfl

theorem cell20_393266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_393266 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393266 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393266 prefixEnd_393266 := by exact prefixLift 393266
  have htrace : WordTrace (prefixWord ++ tailWord_393266) baseStart_393266 baseEnd_393266 := by
    simpa [prefixWord, tailWord_393266, baseEnd_393266] using wordTrace_append hprefix tailTrace_393266
  have hstable : (prefixWord ++ tailWord_393266).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393266).length < 2 ^ (prefixWord ++ tailWord_393266).sum := by decide
  have hdescent : baseEnd_393266 < baseStart_393266 := by decide
  rcases family_descends (prefixWord ++ tailWord_393266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393276 : List Nat := [2, 2, 2, 2, 2, 1, 5, 1, 3]
def baseStart_393276 : Nat := 118140960795 + 393276 * 2 ^ 59
def prefixEnd_393276 : Nat := 4983230072969 + 3 ^ 40 * 393276 * 2
def baseEnd_393276 : Nat := 179501882557963146258989

theorem tailTrace_393276 : CollatzResearch.WordTrace tailWord_393276 prefixEnd_393276 179501882557963146258989 := by
  unfold tailWord_393276
  simp only [CollatzResearch.WordTrace]
  refine ⟨7171977061617846519267841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9562636082157128692357121 7171977061617846519267841)
  ·
    refine ⟨5378982796213384889450881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7171977061617846519267841 5378982796213384889450881)
    ·
      refine ⟨4034237097160038667088161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5378982796213384889450881 4034237097160038667088161)
      ·
        refine ⟨3025677822870029000316121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4034237097160038667088161 3025677822870029000316121)
        ·
          refine ⟨2269258367152521750237091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3025677822870029000316121 2269258367152521750237091)
          ·
            refine ⟨3403887550728782625355637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2269258367152521750237091 3403887550728782625355637)
            ·
              refine ⟨319114457880823371127091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3403887550728782625355637 319114457880823371127091)
              ·
                refine ⟨478671686821235056690637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319114457880823371127091 478671686821235056690637)
                ·
                  refine ⟨179501882557963146258989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478671686821235056690637 179501882557963146258989)
                  ·
                    rfl

theorem cell20_393276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3].length) (baseStart_393276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393276 prefixEnd_393276 := by exact prefixLift 393276
  have htrace : WordTrace (prefixWord ++ tailWord_393276) baseStart_393276 baseEnd_393276 := by
    simpa [prefixWord, tailWord_393276, baseEnd_393276] using wordTrace_append hprefix tailTrace_393276
  have hstable : (prefixWord ++ tailWord_393276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393276).length < 2 ^ (prefixWord ++ tailWord_393276).sum := by decide
  have hdescent : baseEnd_393276 < baseStart_393276 := by decide
  rcases family_descends (prefixWord ++ tailWord_393276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393335 : List Nat := [1, 1, 3, 1, 1, 6, 1, 3, 3]
def baseStart_393335 : Nat := 118140960795 + 393335 * 2 ^ 59
def prefixEnd_393335 : Nat := 4983230072969 + 3 ^ 40 * 393335 * 2
def baseEnd_393335 : Nat := 179528811765621163292081

theorem tailTrace_393335 : CollatzResearch.WordTrace tailWord_393335 prefixEnd_393335 179528811765621163292081 := by
  unfold tailWord_393335
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346106030021946114933459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9564070686681297409955639 14346106030021946114933459)
  ·
    refine ⟨21519159045032919172400189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14346106030021946114933459 21519159045032919172400189)
    ·
      refine ⟨8069684641887344689650071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21519159045032919172400189 8069684641887344689650071)
      ·
        refine ⟨12104526962831017034475107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069684641887344689650071 12104526962831017034475107)
        ·
          refine ⟨18156790444246525551712661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12104526962831017034475107 18156790444246525551712661)
          ·
            refine ⟨851099552074055885236531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18156790444246525551712661 851099552074055885236531)
            ·
              refine ⟨1276649328111083827854797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851099552074055885236531 1276649328111083827854797)
              ·
                refine ⟨478743498041656435445549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1276649328111083827854797 478743498041656435445549)
                ·
                  refine ⟨179528811765621163292081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478743498041656435445549 179528811765621163292081)
                  ·
                    rfl

theorem cell20_393335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 6, 1, 3, 3].length) (baseStart_393335 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393335 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393335 prefixEnd_393335 := by exact prefixLift 393335
  have htrace : WordTrace (prefixWord ++ tailWord_393335) baseStart_393335 baseEnd_393335 := by
    simpa [prefixWord, tailWord_393335, baseEnd_393335] using wordTrace_append hprefix tailTrace_393335
  have hstable : (prefixWord ++ tailWord_393335).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393335).length < 2 ^ (prefixWord ++ tailWord_393335).sum := by decide
  have hdescent : baseEnd_393335 < baseStart_393335 := by decide
  rcases family_descends (prefixWord ++ tailWord_393335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393349 : List Nat := [1, 3, 1, 1, 5, 1, 2, 6]
def baseStart_393349 : Nat := 118140960795 + 393349 * 2 ^ 59
def prefixEnd_393349 : Nat := 4983230072969 + 3 ^ 40 * 393349 * 2
def baseEnd_393349 : Nat := 59845067249033112275119

theorem tailTrace_393349 : CollatzResearch.WordTrace tailWord_393349 prefixEnd_393349 59845067249033112275119 := by
  unfold tailWord_393349
  simp only [CollatzResearch.WordTrace]
  refine ⟨14346616651971226505943101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9564411101314151003962067 14346616651971226505943101)
  ·
    refine ⟨5379981244489209939728663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14346616651971226505943101 5379981244489209939728663)
    ·
      refine ⟨8069971866733814909592995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5379981244489209939728663 8069971866733814909592995)
      ·
        refine ⟨12104957800100722364389493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8069971866733814909592995 12104957800100722364389493)
        ·
          refine ⟨1134839793759442721661515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12104957800100722364389493 1134839793759442721661515)
          ·
            refine ⟨1702259690639164082492273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1134839793759442721661515 1702259690639164082492273)
            ·
              refine ⟨1276694767979373061869205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1702259690639164082492273 1276694767979373061869205)
              ·
                refine ⟨59845067249033112275119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1276694767979373061869205 59845067249033112275119)
                ·
                  rfl

theorem cell20_393349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 2, 6].length) (baseStart_393349 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393349 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393349 prefixEnd_393349 := by exact prefixLift 393349
  have htrace : WordTrace (prefixWord ++ tailWord_393349) baseStart_393349 baseEnd_393349 := by
    simpa [prefixWord, tailWord_393349, baseEnd_393349] using wordTrace_append hprefix tailTrace_393349
  have hstable : (prefixWord ++ tailWord_393349).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393349).length < 2 ^ (prefixWord ++ tailWord_393349).sum := by decide
  have hdescent : baseEnd_393349 < baseStart_393349 := by decide
  rcases family_descends (prefixWord ++ tailWord_393349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393373 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 3]
def baseStart_393373 : Nat := 118140960795 + 393373 * 2 ^ 59
def prefixEnd_393373 : Nat := 4983230072969 + 3 ^ 40 * 393373 * 2
def baseEnd_393373 : Nat := 179546156001061920025259

theorem tailTrace_393373 : CollatzResearch.WordTrace tailWord_393373 prefixEnd_393373 179546156001061920025259 := by
  unfold tailWord_393373
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347492003884278604816773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9564994669256185736544515 14347492003884278604816773)
  ·
    refine ⟨2690154750728302238403145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14347492003884278604816773 2690154750728302238403145)
    ·
      refine ⟨2017616063046226678802359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2690154750728302238403145 2017616063046226678802359)
      ·
        refine ⟨3026424094569340018203539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2017616063046226678802359 3026424094569340018203539)
        ·
          refine ⟨4539636141854010027305309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3026424094569340018203539 4539636141854010027305309)
          ·
            refine ⟨1702363553195253760239491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4539636141854010027305309 1702363553195253760239491)
            ·
              refine ⟨2553545329792880640359237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1702363553195253760239491 2553545329792880640359237)
              ·
                refine ⟨478789749336165120067357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2553545329792880640359237 478789749336165120067357)
                ·
                  refine ⟨179546156001061920025259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478789749336165120067357 179546156001061920025259)
                  ·
                    rfl

theorem cell20_393373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_393373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393373 prefixEnd_393373 := by exact prefixLift 393373
  have htrace : WordTrace (prefixWord ++ tailWord_393373) baseStart_393373 baseEnd_393373 := by
    simpa [prefixWord, tailWord_393373, baseEnd_393373] using wordTrace_append hprefix tailTrace_393373
  have hstable : (prefixWord ++ tailWord_393373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393373).length < 2 ^ (prefixWord ++ tailWord_393373).sum := by decide
  have hdescent : baseEnd_393373 < baseStart_393373 := by decide
  rcases family_descends (prefixWord ++ tailWord_393373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393376 : List Nat := [2, 1, 1, 4, 2, 2, 4, 2, 2]
def baseStart_393376 : Nat := 118140960795 + 393376 * 2 ^ 59
def prefixEnd_393376 : Nat := 4983230072969 + 3 ^ 40 * 393376 * 2
def baseEnd_393376 : Nat := 179547525282807242925247

theorem tailTrace_393376 : CollatzResearch.WordTrace tailWord_393376 prefixEnd_393376 179547525282807242925247 := by
  unfold tailWord_393376
  simp only [CollatzResearch.WordTrace]
  refine ⟨7173800711436705058587991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9565067615248940078117321 7173800711436705058587991)
  ·
    refine ⟨10760701067155057587881987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7173800711436705058587991 10760701067155057587881987)
    ·
      refine ⟨16141051600732586381822981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10760701067155057587881987 16141051600732586381822981)
      ·
        refine ⟨3026447175137359946591809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16141051600732586381822981 3026447175137359946591809)
        ·
          refine ⟨2269835381353019959943857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3026447175137359946591809 2269835381353019959943857)
          ·
            refine ⟨1702376536014764969957893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2269835381353019959943857 1702376536014764969957893)
            ·
              refine ⟨319195600502768431867105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1702376536014764969957893 319195600502768431867105)
              ·
                refine ⟨239396700377076323900329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319195600502768431867105 239396700377076323900329)
                ·
                  refine ⟨179547525282807242925247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239396700377076323900329 179547525282807242925247)
                  ·
                    rfl

theorem cell20_393376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 4, 2, 2].length) (baseStart_393376 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393376 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393376 prefixEnd_393376 := by exact prefixLift 393376
  have htrace : WordTrace (prefixWord ++ tailWord_393376) baseStart_393376 baseEnd_393376 := by
    simpa [prefixWord, tailWord_393376, baseEnd_393376] using wordTrace_append hprefix tailTrace_393376
  have hstable : (prefixWord ++ tailWord_393376).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393376).length < 2 ^ (prefixWord ++ tailWord_393376).sum := by decide
  have hdescent : baseEnd_393376 < baseStart_393376 := by decide
  rcases family_descends (prefixWord ++ tailWord_393376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393383 : List Nat := [1, 1, 6, 2, 2, 2, 1, 5]
def baseStart_393383 : Nat := 118140960795 + 393383 * 2 ^ 59
def prefixEnd_393383 : Nat := 4983230072969 + 3 ^ 40 * 393383 * 2
def baseEnd_393383 : Nat := 59850240091182109897295

theorem tailTrace_393383 : CollatzResearch.WordTrace tailWord_393383 prefixEnd_393383 59850240091182109897295 := by
  unfold tailWord_393383
  simp only [CollatzResearch.WordTrace]
  refine ⟨14347856733848050312680803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9565237822565366875120535 14347856733848050312680803)
  ·
    refine ⟨21521785100772075469021205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14347856733848050312680803 21521785100772075469021205)
    ·
      refine ⟨1008833676598691037610369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21521785100772075469021205 1008833676598691037610369)
      ·
        refine ⟨756625257449018278207777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1008833676598691037610369 756625257449018278207777)
        ·
          refine ⟨567468943086763708655833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 756625257449018278207777 567468943086763708655833)
          ·
            refine ⟨425601707315072781491875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 567468943086763708655833 425601707315072781491875)
            ·
              refine ⟨638402560972609172237813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425601707315072781491875 638402560972609172237813)
              ·
                refine ⟨59850240091182109897295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638402560972609172237813 59850240091182109897295)
                ·
                  rfl

theorem cell20_393383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 2, 2, 1, 5].length) (baseStart_393383 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393383 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393383 prefixEnd_393383 := by exact prefixLift 393383
  have htrace : WordTrace (prefixWord ++ tailWord_393383) baseStart_393383 baseEnd_393383 := by
    simpa [prefixWord, tailWord_393383, baseEnd_393383] using wordTrace_append hprefix tailTrace_393383
  have hstable : (prefixWord ++ tailWord_393383).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393383).length < 2 ^ (prefixWord ++ tailWord_393383).sum := by decide
  have hdescent : baseEnd_393383 < baseStart_393383 := by decide
  rcases family_descends (prefixWord ++ tailWord_393383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393410 : List Nat := [3, 5, 1, 1, 1, 2, 2, 3, 2]
def baseStart_393410 : Nat := 118140960795 + 393410 * 2 ^ 59
def prefixEnd_393410 : Nat := 4983230072969 + 3 ^ 40 * 393410 * 2
def baseEnd_393410 : Nat := 179563043809254235791775

theorem tailTrace_393410 : CollatzResearch.WordTrace tailWord_393410 prefixEnd_393410 179563043809254235791775 := by
  unfold tailWord_393410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3587210376187558480978421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9565894336500155949275789 3587210376187558480978421)
  ·
    refine ⟨336300972767583607591727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3587210376187558480978421 336300972767583607591727)
    ·
      refine ⟨504451459151375411387591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 336300972767583607591727 504451459151375411387591)
      ·
        refine ⟨756677188727063117081387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 504451459151375411387591 756677188727063117081387)
        ·
          refine ⟨1135015783090594675622081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 756677188727063117081387 1135015783090594675622081)
          ·
            refine ⟨851261837317946006716561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135015783090594675622081 851261837317946006716561)
            ·
              refine ⟨638446377988459505037421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 851261837317946006716561 638446377988459505037421)
              ·
                refine ⟨239417391745672314389033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 638446377988459505037421 239417391745672314389033)
                ·
                  refine ⟨179563043809254235791775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239417391745672314389033 179563043809254235791775)
                  ·
                    rfl

theorem cell20_393410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 2, 3, 2].length) (baseStart_393410 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393410 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393410 prefixEnd_393410 := by exact prefixLift 393410
  have htrace : WordTrace (prefixWord ++ tailWord_393410) baseStart_393410 baseEnd_393410 := by
    simpa [prefixWord, tailWord_393410, baseEnd_393410] using wordTrace_append hprefix tailTrace_393410
  have hstable : (prefixWord ++ tailWord_393410).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393410).length < 2 ^ (prefixWord ++ tailWord_393410).sum := by decide
  have hdescent : baseEnd_393410 < baseStart_393410 := by decide
  rcases family_descends (prefixWord ++ tailWord_393410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393504 : List Nat := [2, 1, 1, 5, 2, 1, 4, 1, 3]
def baseStart_393504 : Nat := 118140960795 + 393504 * 2 ^ 59
def prefixEnd_393504 : Nat := 4983230072969 + 3 ^ 40 * 393504 * 2
def baseEnd_393504 : Nat := 179605947970607686658057

theorem tailTrace_393504 : CollatzResearch.WordTrace tailWord_393504 prefixEnd_393504 179605947970607686658057 := by
  unfold tailWord_393504
  simp only [CollatzResearch.WordTrace]
  refine ⟨7176134983204843988917783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9568179977606458651890377 7176134983204843988917783)
  ·
    refine ⟨10764202474807265983376675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7176134983204843988917783 10764202474807265983376675)
    ·
      refine ⟨16146303712210898975065013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10764202474807265983376675 16146303712210898975065013)
      ·
        refine ⟨1513715973019771778912345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16146303712210898975065013 1513715973019771778912345)
        ·
          refine ⟨1135286979764828834184259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1513715973019771778912345 1135286979764828834184259)
          ·
            refine ⟨1702930469647243251276389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135286979764828834184259 1702930469647243251276389)
            ·
              refine ⟨319299463058858109614323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1702930469647243251276389 319299463058858109614323)
              ·
                refine ⟨478949194588287164421485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319299463058858109614323 478949194588287164421485)
                ·
                  refine ⟨179605947970607686658057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 478949194588287164421485 179605947970607686658057)
                  ·
                    rfl

theorem cell20_393504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 4, 1, 3].length) (baseStart_393504 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393504 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393504 prefixEnd_393504 := by exact prefixLift 393504
  have htrace : WordTrace (prefixWord ++ tailWord_393504) baseStart_393504 baseEnd_393504 := by
    simpa [prefixWord, tailWord_393504, baseEnd_393504] using wordTrace_append hprefix tailTrace_393504
  have hstable : (prefixWord ++ tailWord_393504).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393504).length < 2 ^ (prefixWord ++ tailWord_393504).sum := by decide
  have hdescent : baseEnd_393504 < baseStart_393504 := by decide
  rcases family_descends (prefixWord ++ tailWord_393504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393556 : List Nat := [2, 4, 1, 1, 2, 4, 1, 5]
def baseStart_393556 : Nat := 118140960795 + 393556 * 2 ^ 59
def prefixEnd_393556 : Nat := 4983230072969 + 3 ^ 40 * 393556 * 2
def baseEnd_393556 : Nat := 59876560729175538974837

theorem tailTrace_393556 : CollatzResearch.WordTrace tailWord_393556 prefixEnd_393556 59876560729175538974837 := by
  unfold tailWord_393556
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177083281110650429364261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9569444374814200572485681 7177083281110650429364261)
  ·
    refine ⟨1345703115208246955505799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7177083281110650429364261 1345703115208246955505799)
    ·
      refine ⟨2018554672812370433258699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1345703115208246955505799 2018554672812370433258699)
      ·
        refine ⟨3027832009218555649888049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2018554672812370433258699 3027832009218555649888049)
        ·
          refine ⟨2270874006913916737416037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3027832009218555649888049 2270874006913916737416037)
          ·
            refine ⟨425788876296359388265507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2270874006913916737416037 425788876296359388265507)
            ·
              refine ⟨638683314444539082398261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 425788876296359388265507 638683314444539082398261)
              ·
                refine ⟨59876560729175538974837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638683314444539082398261 59876560729175538974837)
                ·
                  rfl

theorem cell20_393556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_393556 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393556 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393556 prefixEnd_393556 := by exact prefixLift 393556
  have htrace : WordTrace (prefixWord ++ tailWord_393556) baseStart_393556 baseEnd_393556 := by
    simpa [prefixWord, tailWord_393556, baseEnd_393556] using wordTrace_append hprefix tailTrace_393556
  have hstable : (prefixWord ++ tailWord_393556).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393556).length < 2 ^ (prefixWord ++ tailWord_393556).sum := by decide
  have hdescent : baseEnd_393556 < baseStart_393556 := by decide
  rcases family_descends (prefixWord ++ tailWord_393556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393560 : List Nat := [2, 1, 2, 2, 1, 1, 2, 9]
def baseStart_393560 : Nat := 118140960795 + 393560 * 2 ^ 59
def prefixEnd_393560 : Nat := 4983230072969 + 3 ^ 40 * 393560 * 2
def baseEnd_393560 : Nat := 59877169298840126930387

theorem tailTrace_393560 : CollatzResearch.WordTrace tailWord_393560 prefixEnd_393560 59877169298840126930387 := by
  unfold tailWord_393560
  simp only [CollatzResearch.WordTrace]
  refine ⟨7177156227103404770937067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9569541636137873027916089 7177156227103404770937067)
  ·
    refine ⟨10765734340655107156405601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7177156227103404770937067 10765734340655107156405601)
    ·
      refine ⟨8074300755491330367304201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10765734340655107156405601 8074300755491330367304201)
      ·
        refine ⟨6055725566618497775478151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8074300755491330367304201 6055725566618497775478151)
        ·
          refine ⟨9083588349927746663217227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6055725566618497775478151 9083588349927746663217227)
          ·
            refine ⟨13625382524891619994825841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9083588349927746663217227 13625382524891619994825841)
            ·
              refine ⟨10219036893668714996119381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 13625382524891619994825841 10219036893668714996119381)
              ·
                refine ⟨59877169298840126930387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10219036893668714996119381 59877169298840126930387)
                ·
                  rfl

theorem cell20_393560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 9].length) (baseStart_393560 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393560 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393560 prefixEnd_393560 := by exact prefixLift 393560
  have htrace : WordTrace (prefixWord ++ tailWord_393560) baseStart_393560 baseEnd_393560 := by
    simpa [prefixWord, tailWord_393560, baseEnd_393560] using wordTrace_append hprefix tailTrace_393560
  have hstable : (prefixWord ++ tailWord_393560).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393560).length < 2 ^ (prefixWord ++ tailWord_393560).sum := by decide
  have hdescent : baseEnd_393560 < baseStart_393560 := by decide
  rcases family_descends (prefixWord ++ tailWord_393560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393570 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 6]
def baseStart_393570 : Nat := 118140960795 + 393570 * 2 ^ 59
def prefixEnd_393570 : Nat := 4983230072969 + 3 ^ 40 * 393570 * 2
def baseEnd_393570 : Nat := 179636072169004790457787

theorem tailTrace_393570 : CollatzResearch.WordTrace tailWord_393570 prefixEnd_393570 179636072169004790457787 := by
  unfold tailWord_393570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3588669296042645312434541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9569784789447054166492109 3588669296042645312434541)
  ·
    refine ⟨1345750986015991992162953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3588669296042645312434541 1345750986015991992162953)
    ·
      refine ⟨1009313239511993994122215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1345750986015991992162953 1009313239511993994122215)
      ·
        refine ⟨1513969859267990991183323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009313239511993994122215 1513969859267990991183323)
        ·
          refine ⟨2270954788901986486774985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1513969859267990991183323 2270954788901986486774985)
          ·
            refine ⟨1703216091676489865081239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2270954788901986486774985 1703216091676489865081239)
            ·
              refine ⟨2554824137514734797621859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1703216091676489865081239 2554824137514734797621859)
              ·
                refine ⟨3832236206272102196432789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2554824137514734797621859 3832236206272102196432789)
                ·
                  refine ⟨179636072169004790457787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3832236206272102196432789 179636072169004790457787)
                  ·
                    rfl

theorem cell20_393570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_393570 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393570 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393570 prefixEnd_393570 := by exact prefixLift 393570
  have htrace : WordTrace (prefixWord ++ tailWord_393570) baseStart_393570 baseEnd_393570 := by
    simpa [prefixWord, tailWord_393570, baseEnd_393570] using wordTrace_append hprefix tailTrace_393570
  have hstable : (prefixWord ++ tailWord_393570).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393570).length < 2 ^ (prefixWord ++ tailWord_393570).sum := by decide
  have hdescent : baseEnd_393570 < baseStart_393570 := by decide
  rcases family_descends (prefixWord ++ tailWord_393570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393577 : List Nat := [1, 2, 1, 1, 1, 3, 7, 4]
def baseStart_393577 : Nat := 118140960795 + 393577 * 2 ^ 59
def prefixEnd_393577 : Nat := 4983230072969 + 3 ^ 40 * 393577 * 2
def baseEnd_393577 : Nat := 59879755719914625741475

theorem tailTrace_393577 : CollatzResearch.WordTrace tailWord_393577 prefixEnd_393577 59879755719914625741475 := by
  unfold tailWord_393577
  simp only [CollatzResearch.WordTrace]
  refine ⟨14354932495145221445242985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9569954996763480963495323 14354932495145221445242985)
  ·
    refine ⟨10766199371358916083932239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14354932495145221445242985 10766199371358916083932239)
    ·
      refine ⟨16149299057038374125898359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10766199371358916083932239 16149299057038374125898359)
      ·
        refine ⟨24223948585557561188847539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16149299057038374125898359 24223948585557561188847539)
        ·
          refine ⟨36335922878336341783271309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24223948585557561188847539 36335922878336341783271309)
          ·
            refine ⟨13625971079376128168726741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36335922878336341783271309 13625971079376128168726741)
            ·
              refine ⟨319358697172878003954533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13625971079376128168726741 319358697172878003954533)
              ·
                refine ⟨59879755719914625741475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319358697172878003954533 59879755719914625741475)
                ·
                  rfl

theorem cell20_393577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 7, 4].length) (baseStart_393577 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393577 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393577 prefixEnd_393577 := by exact prefixLift 393577
  have htrace : WordTrace (prefixWord ++ tailWord_393577) baseStart_393577 baseEnd_393577 := by
    simpa [prefixWord, tailWord_393577, baseEnd_393577] using wordTrace_append hprefix tailTrace_393577
  have hstable : (prefixWord ++ tailWord_393577).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393577).length < 2 ^ (prefixWord ++ tailWord_393577).sum := by decide
  have hdescent : baseEnd_393577 < baseStart_393577 := by decide
  rcases family_descends (prefixWord ++ tailWord_393577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393601 : List Nat := [1, 2, 4, 3, 1, 2, 1, 1, 5]
def baseStart_393601 : Nat := 118140960795 + 393601 * 2 ^ 59
def prefixEnd_393601 : Nat := 4983230072969 + 3 ^ 40 * 393601 * 2
def baseEnd_393601 : Nat := 179650221413706460424327

theorem tailTrace_393601 : CollatzResearch.WordTrace tailWord_393601 prefixEnd_393601 179650221413706460424327 := by
  unfold tailWord_393601
  simp only [CollatzResearch.WordTrace]
  refine ⟨14355807847058273544116657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9570538564705515696077771 14355807847058273544116657)
  ·
    refine ⟨10766855885293705158087493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14355807847058273544116657 10766855885293705158087493)
    ·
      refine ⟨2018785478492569717141405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10766855885293705158087493 2018785478492569717141405)
      ·
        refine ⟨757044554434713643928027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2018785478492569717141405 757044554434713643928027)
        ·
          refine ⟨1135566831652070465892041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 757044554434713643928027 1135566831652070465892041)
          ·
            refine ⟨851675123739052849419031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1135566831652070465892041 851675123739052849419031)
            ·
              refine ⟨1277512685608579274128547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 851675123739052849419031 1277512685608579274128547)
              ·
                refine ⟨1916269028412868911192821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1277512685608579274128547 1916269028412868911192821)
                ·
                  refine ⟨179650221413706460424327, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1916269028412868911192821 179650221413706460424327)
                  ·
                    rfl

theorem cell20_393601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 1, 1, 5].length) (baseStart_393601 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393601 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393601 prefixEnd_393601 := by exact prefixLift 393601
  have htrace : WordTrace (prefixWord ++ tailWord_393601) baseStart_393601 baseEnd_393601 := by
    simpa [prefixWord, tailWord_393601, baseEnd_393601] using wordTrace_append hprefix tailTrace_393601
  have hstable : (prefixWord ++ tailWord_393601).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393601).length < 2 ^ (prefixWord ++ tailWord_393601).sum := by decide
  have hdescent : baseEnd_393601 < baseStart_393601 := by decide
  rcases family_descends (prefixWord ++ tailWord_393601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393608 : List Nat := [2, 1, 3, 3, 1, 1, 4, 1, 4]
def baseStart_393608 : Nat := 118140960795 + 393608 * 2 ^ 59
def prefixEnd_393608 : Nat := 4983230072969 + 3 ^ 40 * 393608 * 2
def baseEnd_393608 : Nat := 179653416404445547190965

theorem tailTrace_393608 : CollatzResearch.WordTrace tailWord_393608 prefixEnd_393608 179653416404445547190965 := by
  unfold tailWord_393608
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178031579016456869810739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9570708772021942493080985 7178031579016456869810739)
  ·
    refine ⟨10767047368524685304716109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7178031579016456869810739 10767047368524685304716109)
    ·
      refine ⟨4037642763196756989268541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10767047368524685304716109 4037642763196756989268541)
      ·
        refine ⟨1514116036198783870975703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4037642763196756989268541 1514116036198783870975703)
        ·
          refine ⟨2271174054298175806463555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514116036198783870975703 2271174054298175806463555)
          ·
            refine ⟨3406761081447263709695333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2271174054298175806463555 3406761081447263709695333)
            ·
              refine ⟨638767702771361945567875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3406761081447263709695333 638767702771361945567875)
              ·
                refine ⟨958151554157042918351813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 638767702771361945567875 958151554157042918351813)
                ·
                  refine ⟨179653416404445547190965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958151554157042918351813 179653416404445547190965)
                  ·
                    rfl

theorem cell20_393608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 1, 4].length) (baseStart_393608 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393608 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393608 prefixEnd_393608 := by exact prefixLift 393608
  have htrace : WordTrace (prefixWord ++ tailWord_393608) baseStart_393608 baseEnd_393608 := by
    simpa [prefixWord, tailWord_393608, baseEnd_393608] using wordTrace_append hprefix tailTrace_393608
  have hstable : (prefixWord ++ tailWord_393608).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393608).length < 2 ^ (prefixWord ++ tailWord_393608).sum := by decide
  have hdescent : baseEnd_393608 < baseStart_393608 := by decide
  rcases family_descends (prefixWord ++ tailWord_393608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393632 : List Nat := [2, 1, 1, 4, 1, 5, 2, 4]
def baseStart_393632 : Nat := 118140960795 + 393632 * 2 ^ 59
def prefixEnd_393632 : Nat := 4983230072969 + 3 ^ 40 * 393632 * 2
def baseEnd_393632 : Nat := 59888123552802710130289

theorem tailTrace_393632 : CollatzResearch.WordTrace tailWord_393632 prefixEnd_393632 59888123552802710130289 := by
  unfold tailWord_393632
  simp only [CollatzResearch.WordTrace]
  refine ⟨7178469254972982919247575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9571292339963977225663433 7178469254972982919247575)
  ·
    refine ⟨10767703882459474378871363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7178469254972982919247575 10767703882459474378871363)
    ·
      refine ⟨16151555823689211568307045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10767703882459474378871363 16151555823689211568307045)
      ·
        refine ⟨3028416716941727169057571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16151555823689211568307045 3028416716941727169057571)
        ·
          refine ⟨4542625075412590753586357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3028416716941727169057571 4542625075412590753586357)
          ·
            refine ⟨425871100819930383148721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4542625075412590753586357 425871100819930383148721)
            ·
              refine ⟨319403325614947787361541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425871100819930383148721 319403325614947787361541)
              ·
                refine ⟨59888123552802710130289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319403325614947787361541 59888123552802710130289)
                ·
                  rfl

theorem cell20_393632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 5, 2, 4].length) (baseStart_393632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393632 prefixEnd_393632 := by exact prefixLift 393632
  have htrace : WordTrace (prefixWord ++ tailWord_393632) baseStart_393632 baseEnd_393632 := by
    simpa [prefixWord, tailWord_393632, baseEnd_393632] using wordTrace_append hprefix tailTrace_393632
  have hstable : (prefixWord ++ tailWord_393632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393632).length < 2 ^ (prefixWord ++ tailWord_393632).sum := by decide
  have hdescent : baseEnd_393632 < baseStart_393632 := by decide
  rcases family_descends (prefixWord ++ tailWord_393632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393714 : List Nat := [3, 2, 1, 4, 3, 1, 2, 2, 2]
def baseStart_393714 : Nat := 118140960795 + 393714 * 2 ^ 59
def prefixEnd_393714 : Nat := 4983230072969 + 3 ^ 40 * 393714 * 2
def baseEnd_393714 : Nat := 179701797692780289657199

theorem tailTrace_393714 : CollatzResearch.WordTrace tailWord_393714 prefixEnd_393714 179701797692780289657199 := by
  unfold tailWord_393714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3589982323912223460745049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9573286197099262561986797 3589982323912223460745049)
  ·
    refine ⟨2692486742934167595558787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3589982323912223460745049 2692486742934167595558787)
    ·
      refine ⟨4038730114401251393338181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2692486742934167595558787 4038730114401251393338181)
      ·
        refine ⟨757261896450234636250909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4038730114401251393338181 757261896450234636250909)
        ·
          refine ⟨283973211168837988594091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757261896450234636250909 283973211168837988594091)
          ·
            refine ⟨425959816753256982891137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 283973211168837988594091 425959816753256982891137)
            ·
              refine ⟨319469862564942737168353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 425959816753256982891137 319469862564942737168353)
              ·
                refine ⟨239602396923707052876265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319469862564942737168353 239602396923707052876265)
                ·
                  refine ⟨179701797692780289657199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239602396923707052876265 179701797692780289657199)
                  ·
                    rfl

theorem cell20_393714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 2, 2, 2].length) (baseStart_393714 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393714 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393714 prefixEnd_393714 := by exact prefixLift 393714
  have htrace : WordTrace (prefixWord ++ tailWord_393714) baseStart_393714 baseEnd_393714 := by
    simpa [prefixWord, tailWord_393714, baseEnd_393714] using wordTrace_append hprefix tailTrace_393714
  have hstable : (prefixWord ++ tailWord_393714).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393714).length < 2 ^ (prefixWord ++ tailWord_393714).sum := by decide
  have hdescent : baseEnd_393714 < baseStart_393714 := by decide
  rcases family_descends (prefixWord ++ tailWord_393714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393719 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 9]
def baseStart_393719 : Nat := 118140960795 + 393719 * 2 ^ 59
def prefixEnd_393719 : Nat := 4983230072969 + 3 ^ 40 * 393719 * 2
def baseEnd_393719 : Nat := 179704079829022494490511

theorem tailTrace_393719 : CollatzResearch.WordTrace tailWord_393719 prefixEnd_393719 179704079829022494490511 := by
  unfold tailWord_393719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14360111660630779696912211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9573407773753853131274807 14360111660630779696912211)
  ·
    refine ⟨21540167490946169545368317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14360111660630779696912211 21540167490946169545368317)
    ·
      refine ⟨8077562809104813579513119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21540167490946169545368317 8077562809104813579513119)
      ·
        refine ⟨12116344213657220369269679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8077562809104813579513119 12116344213657220369269679)
        ·
          refine ⟨18174516320485830553904519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12116344213657220369269679 18174516320485830553904519)
          ·
            refine ⟨27261774480728745830856779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18174516320485830553904519 27261774480728745830856779)
            ·
              refine ⟨40892661721093118746285169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 27261774480728745830856779 40892661721093118746285169)
              ·
                refine ⟨30669496290819839059713877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 40892661721093118746285169 30669496290819839059713877)
                ·
                  refine ⟨179704079829022494490511, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30669496290819839059713877 179704079829022494490511)
                  ·
                    rfl

theorem cell20_393719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 9].length) (baseStart_393719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393719 prefixEnd_393719 := by exact prefixLift 393719
  have htrace : WordTrace (prefixWord ++ tailWord_393719) baseStart_393719 baseEnd_393719 := by
    simpa [prefixWord, tailWord_393719, baseEnd_393719] using wordTrace_append hprefix tailTrace_393719
  have hstable : (prefixWord ++ tailWord_393719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393719).length < 2 ^ (prefixWord ++ tailWord_393719).sum := by decide
  have hdescent : baseEnd_393719 < baseStart_393719 := by decide
  rcases family_descends (prefixWord ++ tailWord_393719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393729 : List Nat := [1, 2, 4, 1, 3, 1, 3, 5]
def baseStart_393729 : Nat := 118140960795 + 393729 * 2 ^ 59
def prefixEnd_393729 : Nat := 4983230072969 + 3 ^ 40 * 393729 * 2
def baseEnd_393729 : Nat := 59902881367168968052379

theorem tailTrace_393729 : CollatzResearch.WordTrace tailWord_393729 prefixEnd_393729 59902881367168968052379 := by
  unfold tailWord_393729
  simp only [CollatzResearch.WordTrace]
  refine ⟨14360476390594551404776241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9573650927063034269850827 14360476390594551404776241)
  ·
    refine ⟨10770357292945913553582181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14360476390594551404776241 10770357292945913553582181)
    ·
      refine ⟨2019441992427358791296659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10770357292945913553582181 2019441992427358791296659)
      ·
        refine ⟨3029162988641038186944989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019441992427358791296659 3029162988641038186944989)
        ·
          refine ⟨1135936120740389320104371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3029162988641038186944989 1135936120740389320104371)
          ·
            refine ⟨1703904181110583980156557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1135936120740389320104371 1703904181110583980156557)
            ·
              refine ⟨638964067916468992558709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1703904181110583980156557 638964067916468992558709)
              ·
                refine ⟨59902881367168968052379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 638964067916468992558709 59902881367168968052379)
                ·
                  rfl

theorem cell20_393729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 3, 5].length) (baseStart_393729 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393729 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393729 prefixEnd_393729 := by exact prefixLift 393729
  have htrace : WordTrace (prefixWord ++ tailWord_393729) baseStart_393729 baseEnd_393729 := by
    simpa [prefixWord, tailWord_393729, baseEnd_393729] using wordTrace_append hprefix tailTrace_393729
  have hstable : (prefixWord ++ tailWord_393729).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393729).length < 2 ^ (prefixWord ++ tailWord_393729).sum := by decide
  have hdescent : baseEnd_393729 < baseStart_393729 := by decide
  rcases family_descends (prefixWord ++ tailWord_393729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393770 : List Nat := [3, 1, 4, 1, 1, 4, 1, 2, 3]
def baseStart_393770 : Nat := 118140960795 + 393770 * 2 ^ 59
def prefixEnd_393770 : Nat := 4983230072969 + 3 ^ 40 * 393770 * 2
def baseEnd_393770 : Nat := 179727357618692983790303

theorem tailTrace_393770 : CollatzResearch.WordTrace tailWord_393770 prefixEnd_393770 179727357618692983790303 := by
  unfold tailWord_393770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3590492945861503851754691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9574647855630676938012509 3590492945861503851754691)
  ·
    refine ⟨5385739418792255777632037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3590492945861503851754691 5385739418792255777632037)
    ·
      refine ⟨1009826141023547958306007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5385739418792255777632037 1009826141023547958306007)
      ·
        refine ⟨1514739211535321937459011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1009826141023547958306007 1514739211535321937459011)
        ·
          refine ⟨2272108817302982906188517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1514739211535321937459011 2272108817302982906188517)
          ·
            refine ⟨426020403244309294910347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2272108817302982906188517 426020403244309294910347)
            ·
              refine ⟨639030604866463942365521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426020403244309294910347 639030604866463942365521)
              ·
                refine ⟨479272953649847956774141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639030604866463942365521 479272953649847956774141)
                ·
                  refine ⟨179727357618692983790303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479272953649847956774141 179727357618692983790303)
                  ·
                    rfl

theorem cell20_393770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_393770 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393770 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393770 prefixEnd_393770 := by exact prefixLift 393770
  have htrace : WordTrace (prefixWord ++ tailWord_393770) baseStart_393770 baseEnd_393770 := by
    simpa [prefixWord, tailWord_393770, baseEnd_393770] using wordTrace_append hprefix tailTrace_393770
  have hstable : (prefixWord ++ tailWord_393770).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393770).length < 2 ^ (prefixWord ++ tailWord_393770).sum := by decide
  have hdescent : baseEnd_393770 < baseStart_393770 := by decide
  rcases family_descends (prefixWord ++ tailWord_393770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393773 : List Nat := [1, 5, 4, 1, 1, 1, 2, 1, 4]
def baseStart_393773 : Nat := 118140960795 + 393773 * 2 ^ 59
def prefixEnd_393773 : Nat := 4983230072969 + 3 ^ 40 * 393773 * 2
def baseEnd_393773 : Nat := 179728726900438306690291

theorem tailTrace_393773 : CollatzResearch.WordTrace tailWord_393773 prefixEnd_393773 179728726900438306690291 := by
  unfold tailWord_393773
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362081202435146919377973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9574720801623431279585315 14362081202435146919377973)
  ·
    refine ⟨1346445112728295023691685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 14362081202435146919377973 1346445112728295023691685)
    ·
      refine ⟨252458458636555316942191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1346445112728295023691685 252458458636555316942191)
      ·
        refine ⟨378687687954832975413287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 252458458636555316942191 378687687954832975413287)
        ·
          refine ⟨568031531932249463119931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 378687687954832975413287 568031531932249463119931)
          ·
            refine ⟨852047297898374194679897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568031531932249463119931 852047297898374194679897)
            ·
              refine ⟨639035473423780646009923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 852047297898374194679897 639035473423780646009923)
              ·
                refine ⟨958553210135670969014885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639035473423780646009923 958553210135670969014885)
                ·
                  refine ⟨179728726900438306690291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958553210135670969014885 179728726900438306690291)
                  ·
                    rfl

theorem cell20_393773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 2, 1, 4].length) (baseStart_393773 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393773 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393773 prefixEnd_393773 := by exact prefixLift 393773
  have htrace : WordTrace (prefixWord ++ tailWord_393773) baseStart_393773 baseEnd_393773 := by
    simpa [prefixWord, tailWord_393773, baseEnd_393773] using wordTrace_append hprefix tailTrace_393773
  have hstable : (prefixWord ++ tailWord_393773).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393773).length < 2 ^ (prefixWord ++ tailWord_393773).sum := by decide
  have hdescent : baseEnd_393773 < baseStart_393773 := by decide
  rcases family_descends (prefixWord ++ tailWord_393773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393791 : List Nat := [1, 1, 2, 2, 3, 2, 5, 1, 3]
def baseStart_393791 : Nat := 118140960795 + 393791 * 2 ^ 59
def prefixEnd_393791 : Nat := 4983230072969 + 3 ^ 40 * 393791 * 2
def baseEnd_393791 : Nat := 179736942590910244090217

theorem tailTrace_393791 : CollatzResearch.WordTrace tailWord_393791 prefixEnd_393791 179736942590910244090217 := by
  unfold tailWord_393791
  simp only [CollatzResearch.WordTrace]
  refine ⟨14362737716369935993533227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9575158477579957329022151 14362737716369935993533227)
  ·
    refine ⟨21544106574554903990299841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14362737716369935993533227 21544106574554903990299841)
    ·
      refine ⟨16158079930916177992724881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21544106574554903990299841 16158079930916177992724881)
      ·
        refine ⟨12118559948187133494543661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16158079930916177992724881 12118559948187133494543661)
        ·
          refine ⟨4544459980570175060453873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12118559948187133494543661 4544459980570175060453873)
          ·
            refine ⟨3408344985427631295340405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4544459980570175060453873 3408344985427631295340405)
            ·
              refine ⟨319532342383840433938163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3408344985427631295340405 319532342383840433938163)
              ·
                refine ⟨479298513575760650907245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319532342383840433938163 479298513575760650907245)
                ·
                  refine ⟨179736942590910244090217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479298513575760650907245 179736942590910244090217)
                  ·
                    rfl

theorem cell20_393791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 5, 1, 3].length) (baseStart_393791 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393791 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393791 prefixEnd_393791 := by exact prefixLift 393791
  have htrace : WordTrace (prefixWord ++ tailWord_393791) baseStart_393791 baseEnd_393791 := by
    simpa [prefixWord, tailWord_393791, baseEnd_393791] using wordTrace_append hprefix tailTrace_393791
  have hstable : (prefixWord ++ tailWord_393791).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393791).length < 2 ^ (prefixWord ++ tailWord_393791).sum := by decide
  have hdescent : baseEnd_393791 < baseStart_393791 := by decide
  rcases family_descends (prefixWord ++ tailWord_393791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393812 : List Nat := [2, 4, 1, 1, 1, 3, 1, 2, 5]
def baseStart_393812 : Nat := 118140960795 + 393812 * 2 ^ 59
def prefixEnd_393812 : Nat := 4983230072969 + 3 ^ 40 * 393812 * 2
def baseEnd_393812 : Nat := 179746527563127504390131

theorem tailTrace_393812 : CollatzResearch.WordTrace tailWord_393812 prefixEnd_393812 179746527563127504390131 := by
  unfold tailWord_393812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7181751824646928290023845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9575669099529237720031793 7181751824646928290023845)
  ·
    refine ⟨1346578467121299054379471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7181751824646928290023845 1346578467121299054379471)
    ·
      refine ⟨2019867700681948581569207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346578467121299054379471 2019867700681948581569207)
      ·
        refine ⟨3029801551022922872353811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2019867700681948581569207 3029801551022922872353811)
        ·
          refine ⟨4544702326534384308530717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3029801551022922872353811 4544702326534384308530717)
          ·
            refine ⟨1704263372450394115699019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4544702326534384308530717 1704263372450394115699019)
            ·
              refine ⟨2556395058675591173548529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1704263372450394115699019 2556395058675591173548529)
              ·
                refine ⟨1917296294006693380161397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2556395058675591173548529 1917296294006693380161397)
                ·
                  refine ⟨179746527563127504390131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1917296294006693380161397 179746527563127504390131)
                  ·
                    rfl

theorem cell20_393812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 1, 2, 5].length) (baseStart_393812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393812 prefixEnd_393812 := by exact prefixLift 393812
  have htrace : WordTrace (prefixWord ++ tailWord_393812) baseStart_393812 baseEnd_393812 := by
    simpa [prefixWord, tailWord_393812, baseEnd_393812] using wordTrace_append hprefix tailTrace_393812
  have hstable : (prefixWord ++ tailWord_393812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393812).length < 2 ^ (prefixWord ++ tailWord_393812).sum := by decide
  have hdescent : baseEnd_393812 < baseStart_393812 := by decide
  rcases family_descends (prefixWord ++ tailWord_393812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393832 : List Nat := [2, 1, 4, 3, 3, 1, 1, 1, 4]
def baseStart_393832 : Nat := 118140960795 + 393832 * 2 ^ 59
def prefixEnd_393832 : Nat := 4983230072969 + 3 ^ 40 * 393832 * 2
def baseEnd_393832 : Nat := 179755656108096323723383

theorem tailTrace_393832 : CollatzResearch.WordTrace tailWord_393832 prefixEnd_393832 179755656108096323723383 := by
  unfold tailWord_393832
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182116554610699997887875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9576155406147599997183833 7182116554610699997887875)
  ·
    refine ⟨10773174831916049996831813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7182116554610699997887875 10773174831916049996831813)
    ·
      refine ⟨2019970280984259374405965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10773174831916049996831813 2019970280984259374405965)
      ·
        refine ⟨757488855369097265402237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2019970280984259374405965 757488855369097265402237)
        ·
          refine ⟨284058320763411474525839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 757488855369097265402237 284058320763411474525839)
          ·
            refine ⟨426087481145117211788759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284058320763411474525839 426087481145117211788759)
            ·
              refine ⟨639131221717675817683139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426087481145117211788759 639131221717675817683139)
              ·
                refine ⟨958696832576513726524709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 639131221717675817683139 958696832576513726524709)
                ·
                  refine ⟨179755656108096323723383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 958696832576513726524709 179755656108096323723383)
                  ·
                    rfl

theorem cell20_393832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 1, 4].length) (baseStart_393832 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393832 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393832 prefixEnd_393832 := by exact prefixLift 393832
  have htrace : WordTrace (prefixWord ++ tailWord_393832) baseStart_393832 baseEnd_393832 := by
    simpa [prefixWord, tailWord_393832, baseEnd_393832] using wordTrace_append hprefix tailTrace_393832
  have hstable : (prefixWord ++ tailWord_393832).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393832).length < 2 ^ (prefixWord ++ tailWord_393832).sum := by decide
  have hdescent : baseEnd_393832 < baseStart_393832 := by decide
  rcases family_descends (prefixWord ++ tailWord_393832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393836 : List Nat := [2, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_393836 : Nat := 118140960795 + 393836 * 2 ^ 59
def prefixEnd_393836 : Nat := 4983230072969 + 3 ^ 40 * 393836 * 2
def baseEnd_393836 : Nat := 179757481817090087590033

theorem tailTrace_393836 : CollatzResearch.WordTrace tailWord_393836 prefixEnd_393836 179757481817090087590033 := by
  unfold tailWord_393836
  simp only [CollatzResearch.WordTrace]
  refine ⟨7182189500603454339460681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9576252667471272452614241 7182189500603454339460681)
  ·
    refine ⟨5386642125452590754595511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7182189500603454339460681 5386642125452590754595511)
    ·
      refine ⟨8079963188178886131893267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5386642125452590754595511 8079963188178886131893267)
      ·
        refine ⟨12119944782268329197839901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8079963188178886131893267 12119944782268329197839901)
        ·
          refine ⟨4544979293350623449189963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12119944782268329197839901 4544979293350623449189963)
          ·
            refine ⟨6817468940025935173784945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4544979293350623449189963 6817468940025935173784945)
            ·
              refine ⟨5113101705019451380338709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6817468940025935173784945 5113101705019451380338709)
              ·
                refine ⟨239676642422786783453377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5113101705019451380338709 239676642422786783453377)
                ·
                  refine ⟨179757481817090087590033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239676642422786783453377 179757481817090087590033)
                  ·
                    rfl

theorem cell20_393836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_393836 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393836 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393836 prefixEnd_393836 := by exact prefixLift 393836
  have htrace : WordTrace (prefixWord ++ tailWord_393836) baseStart_393836 baseEnd_393836 := by
    simpa [prefixWord, tailWord_393836, baseEnd_393836] using wordTrace_append hprefix tailTrace_393836
  have hstable : (prefixWord ++ tailWord_393836).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393836).length < 2 ^ (prefixWord ++ tailWord_393836).sum := by decide
  have hdescent : baseEnd_393836 < baseStart_393836 := by decide
  rcases family_descends (prefixWord ++ tailWord_393836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393846 : List Nat := [5, 1, 1, 2, 3, 1, 1, 3, 3]
def baseStart_393846 : Nat := 118140960795 + 393846 * 2 ^ 59
def prefixEnd_393846 : Nat := 4983230072969 + 3 ^ 40 * 393846 * 2
def baseEnd_393846 : Nat := 179762046089574497256659

theorem tailTrace_393846 : CollatzResearch.WordTrace tailWord_393846 prefixEnd_393846 179762046089574497256659 := by
  unfold tailWord_393846
  simp only [CollatzResearch.WordTrace]
  refine ⟨897796483198167524174087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 9576495820780453591190261 897796483198167524174087)
  ·
    refine ⟨1346694724797251286261131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 897796483198167524174087 1346694724797251286261131)
    ·
      refine ⟨2020042087195876929391697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1346694724797251286261131 2020042087195876929391697)
      ·
        refine ⟨1515031565396907697043773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020042087195876929391697 1515031565396907697043773)
        ·
          refine ⟨568136837023840386391415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1515031565396907697043773 568136837023840386391415)
          ·
            refine ⟨852205255535760579587123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568136837023840386391415 852205255535760579587123)
            ·
              refine ⟨1278307883303640869380685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 852205255535760579587123 1278307883303640869380685)
              ·
                refine ⟨479365456238865326017757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1278307883303640869380685 479365456238865326017757)
                ·
                  refine ⟨179762046089574497256659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479365456238865326017757 179762046089574497256659)
                  ·
                    rfl

theorem cell20_393846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3].length) (baseStart_393846 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393846 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393846 prefixEnd_393846 := by exact prefixLift 393846
  have htrace : WordTrace (prefixWord ++ tailWord_393846) baseStart_393846 baseEnd_393846 := by
    simpa [prefixWord, tailWord_393846, baseEnd_393846] using wordTrace_append hprefix tailTrace_393846
  have hstable : (prefixWord ++ tailWord_393846).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393846).length < 2 ^ (prefixWord ++ tailWord_393846).sum := by decide
  have hdescent : baseEnd_393846 < baseStart_393846 := by decide
  rcases family_descends (prefixWord ++ tailWord_393846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393857 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 6]
def baseStart_393857 : Nat := 118140960795 + 393857 * 2 ^ 59
def prefixEnd_393857 : Nat := 4983230072969 + 3 ^ 40 * 393857 * 2
def baseEnd_393857 : Nat := 179767066789307347889947

theorem tailTrace_393857 : CollatzResearch.WordTrace tailWord_393857 prefixEnd_393857 179767066789307347889947 := by
  unfold tailWord_393857
  simp only [CollatzResearch.WordTrace]
  refine ⟨14365144934130829265435825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9576763289420552843623883 14365144934130829265435825)
  ·
    refine ⟨10773858700598121949076869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14365144934130829265435825 10773858700598121949076869)
    ·
      refine ⟨2020098506362147865451913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10773858700598121949076869 2020098506362147865451913)
      ·
        refine ⟨1515073879771610899088935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2020098506362147865451913 1515073879771610899088935)
        ·
          refine ⟨2272610819657416348633403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515073879771610899088935 2272610819657416348633403)
          ·
            refine ⟨3408916229486124522950105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2272610819657416348633403 3408916229486124522950105)
            ·
              refine ⟨2556687172114593392212579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3408916229486124522950105 2556687172114593392212579)
              ·
                refine ⟨3835030758171890088318869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2556687172114593392212579 3835030758171890088318869)
                ·
                  refine ⟨179767066789307347889947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3835030758171890088318869 179767066789307347889947)
                  ·
                    rfl

theorem cell20_393857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 6].length) (baseStart_393857 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393857 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393857 prefixEnd_393857 := by exact prefixLift 393857
  have htrace : WordTrace (prefixWord ++ tailWord_393857) baseStart_393857 baseEnd_393857 := by
    simpa [prefixWord, tailWord_393857, baseEnd_393857] using wordTrace_append hprefix tailTrace_393857
  have hstable : (prefixWord ++ tailWord_393857).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393857).length < 2 ^ (prefixWord ++ tailWord_393857).sum := by decide
  have hdescent : baseEnd_393857 < baseStart_393857 := by decide
  rcases family_descends (prefixWord ++ tailWord_393857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393919 : List Nat := [1, 1, 2, 2, 2, 5, 3, 4]
def baseStart_393919 : Nat := 118140960795 + 393919 * 2 ^ 59
def prefixEnd_393919 : Nat := 4983230072969 + 3 ^ 40 * 393919 * 2
def baseEnd_393919 : Nat := 59931788426236895941009

theorem tailTrace_393919 : CollatzResearch.WordTrace tailWord_393919 prefixEnd_393919 59931788426236895941009 := by
  unfold tailWord_393919
  simp only [CollatzResearch.WordTrace]
  refine ⟨14367406259906213854192811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9578270839937475902795207 14367406259906213854192811)
  ·
    refine ⟨21551109389859320781289217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14367406259906213854192811 21551109389859320781289217)
    ·
      refine ⟨16163332042394490585966913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21551109389859320781289217 16163332042394490585966913)
      ·
        refine ⟨12122499031795867939475185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16163332042394490585966913 12122499031795867939475185)
        ·
          refine ⟨9091874273846900954606389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12122499031795867939475185 9091874273846900954606389)
          ·
            refine ⟨852363213173146964494349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9091874273846900954606389 852363213173146964494349)
            ·
              refine ⟨319636204939930111685381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852363213173146964494349 319636204939930111685381)
              ·
                refine ⟨59931788426236895941009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319636204939930111685381 59931788426236895941009)
                ·
                  rfl

theorem cell20_393919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 3, 4].length) (baseStart_393919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393919 prefixEnd_393919 := by exact prefixLift 393919
  have htrace : WordTrace (prefixWord ++ tailWord_393919) baseStart_393919 baseEnd_393919 := by
    simpa [prefixWord, tailWord_393919, baseEnd_393919] using wordTrace_append hprefix tailTrace_393919
  have hstable : (prefixWord ++ tailWord_393919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393919).length < 2 ^ (prefixWord ++ tailWord_393919).sum := by decide
  have hdescent : baseEnd_393919 < baseStart_393919 := by decide
  rcases family_descends (prefixWord ++ tailWord_393919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393943 : List Nat := [1, 1, 3, 2, 1, 6, 1, 2, 3]
def baseStart_393943 : Nat := 118140960795 + 393943 * 2 ^ 59
def prefixEnd_393943 : Nat := 4983230072969 + 3 ^ 40 * 393943 * 2
def baseEnd_393943 : Nat := 179806319532673271022929

theorem tailTrace_393943 : CollatzResearch.WordTrace tailWord_393943 prefixEnd_393943 179806319532673271022929 := by
  unfold tailWord_393943
  simp only [CollatzResearch.WordTrace]
  refine ⟨14368281611819265953066483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9578854407879510635377655 14368281611819265953066483)
  ·
    refine ⟨21552422417728898929599725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14368281611819265953066483 21552422417728898929599725)
    ·
      refine ⟨8082158406648337098599897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21552422417728898929599725 8082158406648337098599897)
      ·
        refine ⟨6061618804986252823949923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8082158406648337098599897 6061618804986252823949923)
        ·
          refine ⟨9092428207479379235924885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6061618804986252823949923 9092428207479379235924885)
          ·
            refine ⟨426207572225595901683979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9092428207479379235924885 426207572225595901683979)
            ·
              refine ⟨639311358338393852525969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426207572225595901683979 639311358338393852525969)
              ·
                refine ⟨479483518753795389394477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639311358338393852525969 479483518753795389394477)
                ·
                  refine ⟨179806319532673271022929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479483518753795389394477 179806319532673271022929)
                  ·
                    rfl

theorem cell20_393943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 1, 2, 3].length) (baseStart_393943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393943 prefixEnd_393943 := by exact prefixLift 393943
  have htrace : WordTrace (prefixWord ++ tailWord_393943) baseStart_393943 baseEnd_393943 := by
    simpa [prefixWord, tailWord_393943, baseEnd_393943] using wordTrace_append hprefix tailTrace_393943
  have hstable : (prefixWord ++ tailWord_393943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393943).length < 2 ^ (prefixWord ++ tailWord_393943).sum := by decide
  have hdescent : baseEnd_393943 < baseStart_393943 := by decide
  rcases family_descends (prefixWord ++ tailWord_393943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_393960 : List Nat := [2, 1, 4, 1, 4, 1, 3, 1, 3]
def baseStart_393960 : Nat := 118140960795 + 393960 * 2 ^ 59
def prefixEnd_393960 : Nat := 4983230072969 + 3 ^ 40 * 393960 * 2
def baseEnd_393960 : Nat := 179814078795896767456193

theorem tailTrace_393960 : CollatzResearch.WordTrace tailWord_393960 prefixEnd_393960 179814078795896767456193 := by
  unfold tailWord_393960
  simp only [CollatzResearch.WordTrace]
  refine ⟨7184450826378838928217667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9579267768505118570956889 7184450826378838928217667)
  ·
    refine ⟨10776676239568258392326501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7184450826378838928217667 10776676239568258392326501)
    ·
      refine ⟨2020626794919048448561219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10776676239568258392326501 2020626794919048448561219)
      ·
        refine ⟨3030940192378572672841829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2020626794919048448561219 3030940192378572672841829)
        ·
          refine ⟨568301286070982376157843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3030940192378572672841829 568301286070982376157843)
          ·
            refine ⟨852451929106473564236765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568301286070982376157843 852451929106473564236765)
            ·
              refine ⟨319669473414927586588787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852451929106473564236765 319669473414927586588787)
              ·
                refine ⟨479504210122391379883181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319669473414927586588787 479504210122391379883181)
                ·
                  refine ⟨179814078795896767456193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479504210122391379883181 179814078795896767456193)
                  ·
                    rfl

theorem cell20_393960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 3, 1, 3].length) (baseStart_393960 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_393960 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_393960 prefixEnd_393960 := by exact prefixLift 393960
  have htrace : WordTrace (prefixWord ++ tailWord_393960) baseStart_393960 baseEnd_393960 := by
    simpa [prefixWord, tailWord_393960, baseEnd_393960] using wordTrace_append hprefix tailTrace_393960
  have hstable : (prefixWord ++ tailWord_393960).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_393960).length < 2 ^ (prefixWord ++ tailWord_393960).sum := by decide
  have hdescent : baseEnd_393960 < baseStart_393960 := by decide
  rcases family_descends (prefixWord ++ tailWord_393960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394005 : List Nat := [1, 3, 2, 1, 2, 2, 5, 2, 2]
def baseStart_394005 : Nat := 118140960795 + 394005 * 2 ^ 59
def prefixEnd_394005 : Nat := 4983230072969 + 3 ^ 40 * 394005 * 2
def baseEnd_394005 : Nat := 179834618022076610956009

theorem tailTrace_394005 : CollatzResearch.WordTrace tailWord_394005 prefixEnd_394005 179834618022076610956009 := by
  unfold tailWord_394005
  simp only [CollatzResearch.WordTrace]
  refine ⟨14370542937594650541823469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9580361958396433694548979 14370542937594650541823469)
  ·
    refine ⟨5388953601597993953183801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14370542937594650541823469 5388953601597993953183801)
    ·
      refine ⟨4041715201198495464887851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5388953601597993953183801 4041715201198495464887851)
      ·
        refine ⟨6062572801797743197331777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4041715201198495464887851 6062572801797743197331777)
        ·
          refine ⟨4546929601348307397998833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6062572801797743197331777 4546929601348307397998833)
          ·
            refine ⟨3410197201011230548499125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4546929601348307397998833 3410197201011230548499125)
            ·
              refine ⟨319705987594802863921793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3410197201011230548499125 319705987594802863921793)
              ·
                refine ⟨239779490696102147941345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319705987594802863921793 239779490696102147941345)
                ·
                  refine ⟨179834618022076610956009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239779490696102147941345 179834618022076610956009)
                  ·
                    rfl

theorem cell20_394005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 5, 2, 2].length) (baseStart_394005 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394005 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394005 prefixEnd_394005 := by exact prefixLift 394005
  have htrace : WordTrace (prefixWord ++ tailWord_394005) baseStart_394005 baseEnd_394005 := by
    simpa [prefixWord, tailWord_394005, baseEnd_394005] using wordTrace_append hprefix tailTrace_394005
  have hstable : (prefixWord ++ tailWord_394005).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394005).length < 2 ^ (prefixWord ++ tailWord_394005).sum := by decide
  have hdescent : baseEnd_394005 < baseStart_394005 := by decide
  rcases family_descends (prefixWord ++ tailWord_394005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394016 : List Nat := [2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_394016 : Nat := 118140960795 + 394016 * 2 ^ 59
def prefixEnd_394016 : Nat := 4983230072969 + 3 ^ 40 * 394016 * 2
def baseEnd_394016 : Nat := 59946546240603153863099

theorem tailTrace_394016 : CollatzResearch.WordTrace tailWord_394016 prefixEnd_394016 59946546240603153863099 := by
  unfold tailWord_394016
  simp only [CollatzResearch.WordTrace]
  refine ⟨7185472070277399710236951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9580629427036532946982601 7185472070277399710236951)
  ·
    refine ⟨10778208105416099565355427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7185472070277399710236951 10778208105416099565355427)
    ·
      refine ⟨16167312158124149348033141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10778208105416099565355427 16167312158124149348033141)
      ·
        refine ⟨1515685514824139001378107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16167312158124149348033141 1515685514824139001378107)
        ·
          refine ⟨2273528272236208502067161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1515685514824139001378107 2273528272236208502067161)
          ·
            refine ⟨1705146204177156376550371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2273528272236208502067161 1705146204177156376550371)
            ·
              refine ⟨2557719306265734564825557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1705146204177156376550371 2557719306265734564825557)
              ·
                refine ⟨59946546240603153863099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2557719306265734564825557 59946546240603153863099)
                ·
                  rfl

theorem cell20_394016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_394016 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394016 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394016 prefixEnd_394016 := by exact prefixLift 394016
  have htrace : WordTrace (prefixWord ++ tailWord_394016) baseStart_394016 baseEnd_394016 := by
    simpa [prefixWord, tailWord_394016, baseEnd_394016] using wordTrace_append hprefix tailTrace_394016
  have hstable : (prefixWord ++ tailWord_394016).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394016).length < 2 ^ (prefixWord ++ tailWord_394016).sum := by decide
  have hdescent : baseEnd_394016 < baseStart_394016 := by decide
  rcases family_descends (prefixWord ++ tailWord_394016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394060 : List Nat := [2, 2, 1, 3, 3, 3, 2, 2, 2]
def baseStart_394060 : Nat := 118140960795 + 394060 * 2 ^ 59
def prefixEnd_394060 : Nat := 4983230072969 + 3 ^ 40 * 394060 * 2
def baseEnd_394060 : Nat := 179859721520740864122451

theorem tailTrace_394060 : CollatzResearch.WordTrace tailWord_394060 prefixEnd_394060 179859721520740864122451 := by
  unfold tailWord_394060
  simp only [CollatzResearch.WordTrace]
  refine ⟨7186274476197697467537817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9581699301596929956717089 7186274476197697467537817)
  ·
    refine ⟨5389705857148273100653363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7186274476197697467537817 5389705857148273100653363)
    ·
      refine ⟨8084558785722409650980045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5389705857148273100653363 8084558785722409650980045)
      ·
        refine ⟨3031709544645903619117517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8084558785722409650980045 3031709544645903619117517)
        ·
          refine ⟨1136891079242213857169069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3031709544645903619117517 1136891079242213857169069)
          ·
            refine ⟨426334154715830196438401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1136891079242213857169069 426334154715830196438401)
            ·
              refine ⟨319750616036872647328801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426334154715830196438401 319750616036872647328801)
              ·
                refine ⟨239812962027654485496601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 319750616036872647328801 239812962027654485496601)
                ·
                  refine ⟨179859721520740864122451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 239812962027654485496601 179859721520740864122451)
                  ·
                    rfl

theorem cell20_394060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 2, 2, 2].length) (baseStart_394060 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394060 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394060 prefixEnd_394060 := by exact prefixLift 394060
  have htrace : WordTrace (prefixWord ++ tailWord_394060) baseStart_394060 baseEnd_394060 := by
    simpa [prefixWord, tailWord_394060, baseEnd_394060] using wordTrace_append hprefix tailTrace_394060
  have hstable : (prefixWord ++ tailWord_394060).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394060).length < 2 ^ (prefixWord ++ tailWord_394060).sum := by decide
  have hdescent : baseEnd_394060 < baseStart_394060 := by decide
  rcases family_descends (prefixWord ++ tailWord_394060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394071 : List Nat := [1, 1, 3, 2, 4, 3, 1, 5]
def baseStart_394071 : Nat := 118140960795 + 394071 * 2 ^ 59
def prefixEnd_394071 : Nat := 4983230072969 + 3 ^ 40 * 394071 * 2
def baseEnd_394071 : Nat := 59954914073491238251913

theorem tailTrace_394071 : CollatzResearch.WordTrace tailWord_394071 prefixEnd_394071 59954914073491238251913 := by
  unfold tailWord_394071
  simp only [CollatzResearch.WordTrace]
  refine ⟨14372950155355543813726067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9581966770237029209150711 14372950155355543813726067)
  ·
    refine ⟨21559425233033315720589101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14372950155355543813726067 21559425233033315720589101)
    ·
      refine ⟨8084784462387493395220913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21559425233033315720589101 8084784462387493395220913)
      ·
        refine ⟨6063588346790620046415685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8084784462387493395220913 6063588346790620046415685)
        ·
          refine ⟨1136922815023241258702941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6063588346790620046415685 1136922815023241258702941)
          ·
            refine ⟨426346055633715472013603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1136922815023241258702941 426346055633715472013603)
            ·
              refine ⟨639519083450573208020405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 426346055633715472013603 639519083450573208020405)
              ·
                refine ⟨59954914073491238251913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 639519083450573208020405 59954914073491238251913)
                ·
                  rfl

theorem cell20_394071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 3, 1, 5].length) (baseStart_394071 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394071 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394071 prefixEnd_394071 := by exact prefixLift 394071
  have htrace : WordTrace (prefixWord ++ tailWord_394071) baseStart_394071 baseEnd_394071 := by
    simpa [prefixWord, tailWord_394071, baseEnd_394071] using wordTrace_append hprefix tailTrace_394071
  have hstable : (prefixWord ++ tailWord_394071).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394071).length < 2 ^ (prefixWord ++ tailWord_394071).sum := by decide
  have hdescent : baseEnd_394071 < baseStart_394071 := by decide
  rcases family_descends (prefixWord ++ tailWord_394071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394106 : List Nat := [3, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_394106 : Nat := 118140960795 + 394106 * 2 ^ 59
def prefixEnd_394106 : Nat := 4983230072969 + 3 ^ 40 * 394106 * 2
def baseEnd_394106 : Nat := 179880717174169148588929

theorem tailTrace_394106 : CollatzResearch.WordTrace tailWord_394106 prefixEnd_394106 179880717174169148588929 := by
  unfold tailWord_394106
  simp only [CollatzResearch.WordTrace]
  refine ⟨3593556677557186197812543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9582817806819163194166781 3593556677557186197812543)
  ·
    refine ⟨5390335016335779296718815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3593556677557186197812543 5390335016335779296718815)
    ·
      refine ⟨8085502524503668945078223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5390335016335779296718815 8085502524503668945078223)
      ·
        refine ⟨12128253786755503417617335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8085502524503668945078223 12128253786755503417617335)
        ·
          refine ⟨18192380680133255126426003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12128253786755503417617335 18192380680133255126426003)
          ·
            refine ⟨27288571020199882689639005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18192380680133255126426003 27288571020199882689639005)
            ·
              refine ⟨10233214132574956008614627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 27288571020199882689639005 10233214132574956008614627)
              ·
                refine ⟨15349821198862434012921941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10233214132574956008614627 15349821198862434012921941)
                ·
                  refine ⟨179880717174169148588929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15349821198862434012921941 179880717174169148588929)
                  ·
                    rfl

theorem cell20_394106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_394106 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394106 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394106 prefixEnd_394106 := by exact prefixLift 394106
  have htrace : WordTrace (prefixWord ++ tailWord_394106) baseStart_394106 baseEnd_394106 := by
    simpa [prefixWord, tailWord_394106, baseEnd_394106] using wordTrace_append hprefix tailTrace_394106
  have hstable : (prefixWord ++ tailWord_394106).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394106).length < 2 ^ (prefixWord ++ tailWord_394106).sum := by decide
  have hdescent : baseEnd_394106 < baseStart_394106 := by decide
  rcases family_descends (prefixWord ++ tailWord_394106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394133 : List Nat := [1, 3, 2, 1, 1, 5, 3, 1, 3]
def baseStart_394133 : Nat := 118140960795 + 394133 * 2 ^ 59
def prefixEnd_394133 : Nat := 4983230072969 + 3 ^ 40 * 394133 * 2
def baseEnd_394133 : Nat := 179893040709877054688819

theorem tailTrace_394133 : CollatzResearch.WordTrace tailWord_394133 prefixEnd_394133 179893040709877054688819 := by
  unfold tailWord_394133
  simp only [CollatzResearch.WordTrace]
  refine ⟨14375211481130928402483053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9583474320753952268322035 14375211481130928402483053)
  ·
    refine ⟨5390704305424098150931145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14375211481130928402483053 5390704305424098150931145)
    ·
      refine ⟨4043028229068073613198359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5390704305424098150931145 4043028229068073613198359)
      ·
        refine ⟨6064542343602110419797539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4043028229068073613198359 6064542343602110419797539)
        ·
          refine ⟨9096813515403165629696309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6064542343602110419797539 9096813515403165629696309)
          ·
            refine ⟨852826267069046777784029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9096813515403165629696309 852826267069046777784029)
            ·
              refine ⟨319809850150892541669011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 852826267069046777784029 319809850150892541669011)
              ·
                refine ⟨479714775226338812503517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319809850150892541669011 479714775226338812503517)
                ·
                  refine ⟨179893040709877054688819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479714775226338812503517 179893040709877054688819)
                  ·
                    rfl

theorem cell20_394133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 3, 1, 3].length) (baseStart_394133 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394133 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394133 prefixEnd_394133 := by exact prefixLift 394133
  have htrace : WordTrace (prefixWord ++ tailWord_394133) baseStart_394133 baseEnd_394133 := by
    simpa [prefixWord, tailWord_394133, baseEnd_394133] using wordTrace_append hprefix tailTrace_394133
  have hstable : (prefixWord ++ tailWord_394133).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394133).length < 2 ^ (prefixWord ++ tailWord_394133).sum := by decide
  have hdescent : baseEnd_394133 < baseStart_394133 := by decide
  rcases family_descends (prefixWord ++ tailWord_394133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394164 : List Nat := [2, 5, 2, 1, 1, 3, 6]
def baseStart_394164 : Nat := 118140960795 + 394164 * 2 ^ 59
def prefixEnd_394164 : Nat := 4983230072969 + 3 ^ 40 * 394164 * 2
def baseEnd_394164 : Nat := 19989687772730969406151

theorem tailTrace_394164 : CollatzResearch.WordTrace tailWord_394164 prefixEnd_394164 19989687772730969406151 := by
  unfold tailWord_394164
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188171072009310348430773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9584228096012413797907697 7188171072009310348430773)
  ·
    refine ⟨673891038000872845165385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7188171072009310348430773 673891038000872845165385)
    ·
      refine ⟨505418278500654633874039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 673891038000872845165385 505418278500654633874039)
      ·
        refine ⟨758127417750981950811059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505418278500654633874039 758127417750981950811059)
        ·
          refine ⟨1137191126626472926216589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758127417750981950811059 1137191126626472926216589)
          ·
            refine ⟨426446672484927347331221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1137191126626472926216589 426446672484927347331221)
            ·
              refine ⟨19989687772730969406151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 426446672484927347331221 19989687772730969406151)
              ·
                rfl

theorem cell20_394164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 3, 6].length) (baseStart_394164 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394164 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394164 prefixEnd_394164 := by exact prefixLift 394164
  have htrace : WordTrace (prefixWord ++ tailWord_394164) baseStart_394164 baseEnd_394164 := by
    simpa [prefixWord, tailWord_394164, baseEnd_394164] using wordTrace_append hprefix tailTrace_394164
  have hstable : (prefixWord ++ tailWord_394164).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394164).length < 2 ^ (prefixWord ++ tailWord_394164).sum := by decide
  have hdescent : baseEnd_394164 < baseStart_394164 := by decide
  rcases family_descends (prefixWord ++ tailWord_394164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394168 : List Nat := [2, 1, 2, 1, 2, 6, 6]
def baseStart_394168 : Nat := 118140960795 + 394168 * 2 ^ 59
def prefixEnd_394168 : Nat := 4983230072969 + 3 ^ 40 * 394168 * 2
def baseEnd_394168 : Nat := 19989890629285832058001

theorem tailTrace_394168 : CollatzResearch.WordTrace tailWord_394168 prefixEnd_394168 19989890629285832058001 := by
  unfold tailWord_394168
  simp only [CollatzResearch.WordTrace]
  refine ⟨7188244018002064690003579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9584325357336086253338105 7188244018002064690003579)
  ·
    refine ⟨10782366027003097035005369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7188244018002064690003579 10782366027003097035005369)
    ·
      refine ⟨8086774520252322776254027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10782366027003097035005369 8086774520252322776254027)
      ·
        refine ⟨12130161780378484164381041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8086774520252322776254027 12130161780378484164381041)
        ·
          refine ⟨9097621335283863123285781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12130161780378484164381041 9097621335283863123285781)
          ·
            refine ⟨426451000091431083904021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9097621335283863123285781 426451000091431083904021)
            ·
              refine ⟨19989890629285832058001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 426451000091431083904021 19989890629285832058001)
              ·
                rfl

theorem cell20_394168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 6].length) (baseStart_394168 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394168 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394168 prefixEnd_394168 := by exact prefixLift 394168
  have htrace : WordTrace (prefixWord ++ tailWord_394168) baseStart_394168 baseEnd_394168 := by
    simpa [prefixWord, tailWord_394168, baseEnd_394168] using wordTrace_append hprefix tailTrace_394168
  have hstable : (prefixWord ++ tailWord_394168).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394168).length < 2 ^ (prefixWord ++ tailWord_394168).sum := by decide
  have hdescent : baseEnd_394168 < baseStart_394168 := by decide
  rcases family_descends (prefixWord ++ tailWord_394168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394226 : List Nat := [3, 2, 1, 5, 1, 1, 2, 2, 3]
def baseStart_394226 : Nat := 118140960795 + 394226 * 2 ^ 59
def prefixEnd_394226 : Nat := 4983230072969 + 3 ^ 40 * 394226 * 2
def baseEnd_394226 : Nat := 179935488443982064588439

theorem tailTrace_394226 : CollatzResearch.WordTrace tailWord_394226 prefixEnd_394226 179935488443982064588439 := by
  unfold tailWord_394226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3594650867448501321404633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9585735646529336857079021 3594650867448501321404633)
  ·
    refine ⟨2695988150586375991053475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3594650867448501321404633 2695988150586375991053475)
    ·
      refine ⟨4043982225879563986580213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2695988150586375991053475 4043982225879563986580213)
      ·
        refine ⟨379123333676209123741895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4043982225879563986580213 379123333676209123741895)
        ·
          refine ⟨568685000514313685612843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379123333676209123741895 568685000514313685612843)
          ·
            refine ⟨853027500771470528419265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568685000514313685612843 853027500771470528419265)
            ·
              refine ⟨639770625578602896314449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853027500771470528419265 639770625578602896314449)
              ·
                refine ⟨479827969183952172235837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 639770625578602896314449 479827969183952172235837)
                ·
                  refine ⟨179935488443982064588439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479827969183952172235837 179935488443982064588439)
                  ·
                    rfl

theorem cell20_394226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_394226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394226 prefixEnd_394226 := by exact prefixLift 394226
  have htrace : WordTrace (prefixWord ++ tailWord_394226) baseStart_394226 baseEnd_394226 := by
    simpa [prefixWord, tailWord_394226, baseEnd_394226] using wordTrace_append hprefix tailTrace_394226
  have hstable : (prefixWord ++ tailWord_394226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394226).length < 2 ^ (prefixWord ++ tailWord_394226).sum := by decide
  have hdescent : baseEnd_394226 < baseStart_394226 := by decide
  rcases family_descends (prefixWord ++ tailWord_394226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394261 : List Nat := [1, 3, 2, 1, 4, 2, 3, 4]
def baseStart_394261 : Nat := 118140960795 + 394261 * 2 ^ 59
def prefixEnd_394261 : Nat := 4983230072969 + 3 ^ 40 * 394261 * 2
def baseEnd_394261 : Nat := 59983821132559166140543

theorem tailTrace_394261 : CollatzResearch.WordTrace tailWord_394261 prefixEnd_394261 59983821132559166140543 := by
  unfold tailWord_394261
  simp only [CollatzResearch.WordTrace]
  refine ⟨14379880024667206263142637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586586683111470842095091 14379880024667206263142637)
  ·
    refine ⟨5392455009250202348678489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14379880024667206263142637 5392455009250202348678489)
    ·
      refine ⟨4044341256937651761508867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5392455009250202348678489 4044341256937651761508867)
      ·
        refine ⟨6066511885406477642263301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4044341256937651761508867 6066511885406477642263301)
        ·
          refine ⟨1137470978513714557924369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6066511885406477642263301 1137470978513714557924369)
          ·
            refine ⟨853103233885285918443277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137470978513714557924369 853103233885285918443277)
            ·
              refine ⟨319913712706982219416229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853103233885285918443277 319913712706982219416229)
              ·
                refine ⟨59983821132559166140543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 319913712706982219416229 59983821132559166140543)
                ·
                  rfl

theorem cell20_394261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 3, 4].length) (baseStart_394261 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394261 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394261 prefixEnd_394261 := by exact prefixLift 394261
  have htrace : WordTrace (prefixWord ++ tailWord_394261) baseStart_394261 baseEnd_394261 := by
    simpa [prefixWord, tailWord_394261, baseEnd_394261] using wordTrace_append hprefix tailTrace_394261
  have hstable : (prefixWord ++ tailWord_394261).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394261).length < 2 ^ (prefixWord ++ tailWord_394261).sum := by decide
  have hdescent : baseEnd_394261 < baseStart_394261 := by decide
  rcases family_descends (prefixWord ++ tailWord_394261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394265 : List Nat := [1, 2, 1, 2, 1, 1, 4, 8]
def baseStart_394265 : Nat := 118140960795 + 394265 * 2 ^ 59
def prefixEnd_394265 : Nat := 4983230072969 + 3 ^ 40 * 394265 * 2
def baseEnd_394265 : Nat := 59984429702223754096093

theorem tailTrace_394265 : CollatzResearch.WordTrace tailWord_394265 prefixEnd_394265 59984429702223754096093 := by
  unfold tailWord_394265
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380025916652714946288249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9586683944435143297525499 14380025916652714946288249)
  ·
    refine ⟨10785019437489536209716187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14380025916652714946288249 10785019437489536209716187)
    ·
      refine ⟨16177529156234304314574281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10785019437489536209716187 16177529156234304314574281)
      ·
        refine ⟨12133146867175728235930711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16177529156234304314574281 12133146867175728235930711)
        ·
          refine ⟨18199720300763592353896067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12133146867175728235930711 18199720300763592353896067)
          ·
            refine ⟨27299580451145388530844101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18199720300763592353896067 27299580451145388530844101)
            ·
              refine ⟨5118671334589760349533269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27299580451145388530844101 5118671334589760349533269)
              ·
                refine ⟨59984429702223754096093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5118671334589760349533269 59984429702223754096093)
                ·
                  rfl

theorem cell20_394265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 8].length) (baseStart_394265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394265 prefixEnd_394265 := by exact prefixLift 394265
  have htrace : WordTrace (prefixWord ++ tailWord_394265) baseStart_394265 baseEnd_394265 := by
    simpa [prefixWord, tailWord_394265, baseEnd_394265] using wordTrace_append hprefix tailTrace_394265
  have hstable : (prefixWord ++ tailWord_394265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394265).length < 2 ^ (prefixWord ++ tailWord_394265).sum := by decide
  have hdescent : baseEnd_394265 < baseStart_394265 := by decide
  rcases family_descends (prefixWord ++ tailWord_394265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394289 : List Nat := [1, 2, 2, 3, 1, 2, 3, 1, 5]
def baseStart_394289 : Nat := 118140960795 + 394289 * 2 ^ 59
def prefixEnd_394289 : Nat := 4983230072969 + 3 ^ 40 * 394289 * 2
def baseEnd_394289 : Nat := 179964243360633845488181

theorem tailTrace_394289 : CollatzResearch.WordTrace tailWord_394289 prefixEnd_394289 179964243360633845488181 := by
  unfold tailWord_394289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14380901268565767045161921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9587267512377178030107947 14380901268565767045161921)
  ·
    refine ⟨10785675951424325283871441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14380901268565767045161921 10785675951424325283871441)
    ·
      refine ⟨8089256963568243962903581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10785675951424325283871441 8089256963568243962903581)
      ·
        refine ⟨3033471361338091486088843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8089256963568243962903581 3033471361338091486088843)
        ·
          refine ⟨4550207042007137229133265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3033471361338091486088843 4550207042007137229133265)
          ·
            refine ⟨3412655281505352921849949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4550207042007137229133265 3412655281505352921849949)
            ·
              refine ⟨1279745730564507345693731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3412655281505352921849949 1279745730564507345693731)
              ·
                refine ⟨1919618595846761018540597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1279745730564507345693731 1919618595846761018540597)
                ·
                  refine ⟨179964243360633845488181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1919618595846761018540597 179964243360633845488181)
                  ·
                    rfl

theorem cell20_394289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 3, 1, 5].length) (baseStart_394289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394289 prefixEnd_394289 := by exact prefixLift 394289
  have htrace : WordTrace (prefixWord ++ tailWord_394289) baseStart_394289 baseEnd_394289 := by
    simpa [prefixWord, tailWord_394289, baseEnd_394289] using wordTrace_append hprefix tailTrace_394289
  have hstable : (prefixWord ++ tailWord_394289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394289).length < 2 ^ (prefixWord ++ tailWord_394289).sum := by decide
  have hdescent : baseEnd_394289 < baseStart_394289 := by decide
  rcases family_descends (prefixWord ++ tailWord_394289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394292 : List Nat := [2, 5, 1, 2, 1, 1, 1, 3, 4]
def baseStart_394292 : Nat := 118140960795 + 394292 * 2 ^ 59
def prefixEnd_394292 : Nat := 4983230072969 + 3 ^ 40 * 394292 * 2
def baseEnd_394292 : Nat := 179965612642379168388169

theorem tailTrace_394292 : CollatzResearch.WordTrace tailWord_394292 prefixEnd_394292 179965612642379168388169 := by
  unfold tailWord_394292
  simp only [CollatzResearch.WordTrace]
  refine ⟨7190505343777449278760565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9587340458369932371680753 7190505343777449278760565)
  ·
    refine ⟨674109875979135869883803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7190505343777449278760565 674109875979135869883803)
    ·
      refine ⟨1011164813968703804825705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674109875979135869883803 1011164813968703804825705)
      ·
        refine ⟨758373610476527853619279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1011164813968703804825705 758373610476527853619279)
        ·
          refine ⟨1137560415714791780428919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758373610476527853619279 1137560415714791780428919)
          ·
            refine ⟨1706340623572187670643379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1137560415714791780428919 1706340623572187670643379)
            ·
              refine ⟨2559510935358281505965069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1706340623572187670643379 2559510935358281505965069)
              ·
                refine ⟨959816600759355564736901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2559510935358281505965069 959816600759355564736901)
                ·
                  refine ⟨179965612642379168388169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 959816600759355564736901 179965612642379168388169)
                  ·
                    rfl

theorem cell20_394292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 1, 1, 3, 4].length) (baseStart_394292 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394292 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394292 prefixEnd_394292 := by exact prefixLift 394292
  have htrace : WordTrace (prefixWord ++ tailWord_394292) baseStart_394292 baseEnd_394292 := by
    simpa [prefixWord, tailWord_394292, baseEnd_394292] using wordTrace_append hprefix tailTrace_394292
  have hstable : (prefixWord ++ tailWord_394292).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394292).length < 2 ^ (prefixWord ++ tailWord_394292).sum := by decide
  have hdescent : baseEnd_394292 < baseStart_394292 := by decide
  rcases family_descends (prefixWord ++ tailWord_394292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394302 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 3]
def baseStart_394302 : Nat := 118140960795 + 394302 * 2 ^ 59
def prefixEnd_394302 : Nat := 4983230072969 + 3 ^ 40 * 394302 * 2
def baseEnd_394302 : Nat := 179970176914863578054795

theorem tailTrace_394302 : CollatzResearch.WordTrace tailWord_394302 prefixEnd_394302 179970176914863578054795 := by
  unfold tailWord_394302
  simp only [CollatzResearch.WordTrace]
  refine ⟨1797671927189833783173145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9587583611679113510256773 1797671927189833783173145)
  ·
    refine ⟨1348253945392375337379859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1797671927189833783173145 1348253945392375337379859)
    ·
      refine ⟨2022380918088563006069789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1348253945392375337379859 2022380918088563006069789)
      ·
        refine ⟨758392844283211127276171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2022380918088563006069789 758392844283211127276171)
        ·
          refine ⟨1137589266424816690914257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 758392844283211127276171 1137589266424816690914257)
          ·
            refine ⟨853191949818612518185693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1137589266424816690914257 853191949818612518185693)
            ·
              refine ⟨319946981181979694319635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 853191949818612518185693 319946981181979694319635)
              ·
                refine ⟨479920471772969541479453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319946981181979694319635 479920471772969541479453)
                ·
                  refine ⟨179970176914863578054795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479920471772969541479453 179970176914863578054795)
                  ·
                    rfl

theorem cell20_394302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_394302 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394302 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394302 prefixEnd_394302 := by exact prefixLift 394302
  have htrace : WordTrace (prefixWord ++ tailWord_394302) baseStart_394302 baseEnd_394302 := by
    simpa [prefixWord, tailWord_394302, baseEnd_394302] using wordTrace_append hprefix tailTrace_394302
  have hstable : (prefixWord ++ tailWord_394302).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394302).length < 2 ^ (prefixWord ++ tailWord_394302).sum := by decide
  have hdescent : baseEnd_394302 < baseStart_394302 := by decide
  rcases family_descends (prefixWord ++ tailWord_394302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394303 : List Nat := [1, 1, 2, 2, 3, 1, 1, 9]
def baseStart_394303 : Nat := 118140960795 + 394303 * 2 ^ 59
def prefixEnd_394303 : Nat := 4983230072969 + 3 ^ 40 * 394303 * 2
def baseEnd_394303 : Nat := 59990211114037339673819

theorem tailTrace_394303 : CollatzResearch.WordTrace tailWord_394303 prefixEnd_394303 59990211114037339673819 := by
  unfold tailWord_394303
  simp only [CollatzResearch.WordTrace]
  refine ⟨14381411890515047436171563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9587607927010031624114375 14381411890515047436171563)
  ·
    refine ⟨21572117835772571154257345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14381411890515047436171563 21572117835772571154257345)
    ·
      refine ⟨16179088376829428365693009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21572117835772571154257345 16179088376829428365693009)
      ·
        refine ⟨12134316282622071274269757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16179088376829428365693009 12134316282622071274269757)
        ·
          refine ⟨4550368605983276727851159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12134316282622071274269757 4550368605983276727851159)
          ·
            refine ⟨6825552908974915091776739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4550368605983276727851159 6825552908974915091776739)
            ·
              refine ⟨10238329363462372637665109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6825552908974915091776739 10238329363462372637665109)
              ·
                refine ⟨59990211114037339673819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10238329363462372637665109 59990211114037339673819)
                ·
                  rfl

theorem cell20_394303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 9].length) (baseStart_394303 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394303 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394303 prefixEnd_394303 := by exact prefixLift 394303
  have htrace : WordTrace (prefixWord ++ tailWord_394303) baseStart_394303 baseEnd_394303 := by
    simpa [prefixWord, tailWord_394303, baseEnd_394303] using wordTrace_append hprefix tailTrace_394303
  have hstable : (prefixWord ++ tailWord_394303).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394303).length < 2 ^ (prefixWord ++ tailWord_394303).sum := by decide
  have hdescent : baseEnd_394303 < baseStart_394303 := by decide
  rcases family_descends (prefixWord ++ tailWord_394303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394357 : List Nat := [1, 3, 4, 3, 1, 2, 2, 1, 3]
def baseStart_394357 : Nat := 118140960795 + 394357 * 2 ^ 59
def prefixEnd_394357 : Nat := 4983230072969 + 3 ^ 40 * 394357 * 2
def baseEnd_394357 : Nat := 179995280413527831221237

theorem tailTrace_394357 : CollatzResearch.WordTrace tailWord_394357 prefixEnd_394357 179995280413527831221237 := by
  unfold tailWord_394357
  simp only [CollatzResearch.WordTrace]
  refine ⟨14383381432319414658637325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9588920954879609772424883 14383381432319414658637325)
  ·
    refine ⟨5393768037119780496988997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14383381432319414658637325 5393768037119780496988997)
    ·
      refine ⟨1011331506959958843185437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5393768037119780496988997 1011331506959958843185437)
      ·
        refine ⟨379249315109984566194539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1011331506959958843185437 379249315109984566194539)
        ·
          refine ⟨568873972664976849291809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379249315109984566194539 568873972664976849291809)
          ·
            refine ⟨426655479498732636968857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 568873972664976849291809 426655479498732636968857)
            ·
              refine ⟨319991609624049477726643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426655479498732636968857 319991609624049477726643)
              ·
                refine ⟨479987414436074216589965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 319991609624049477726643 479987414436074216589965)
                ·
                  refine ⟨179995280413527831221237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 479987414436074216589965 179995280413527831221237)
                  ·
                    rfl

theorem cell20_394357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 2, 1, 3].length) (baseStart_394357 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394357 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394357 prefixEnd_394357 := by exact prefixLift 394357
  have htrace : WordTrace (prefixWord ++ tailWord_394357) baseStart_394357 baseEnd_394357 := by
    simpa [prefixWord, tailWord_394357, baseEnd_394357] using wordTrace_append hprefix tailTrace_394357
  have hstable : (prefixWord ++ tailWord_394357).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394357).length < 2 ^ (prefixWord ++ tailWord_394357).sum := by decide
  have hdescent : baseEnd_394357 < baseStart_394357 := by decide
  rcases family_descends (prefixWord ++ tailWord_394357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394399 : List Nat := [1, 1, 2, 6, 2, 1, 2, 2, 3]
def baseStart_394399 : Nat := 118140960795 + 394399 * 2 ^ 59
def prefixEnd_394399 : Nat := 4983230072969 + 3 ^ 40 * 394399 * 2
def baseEnd_394399 : Nat := 180014450357962351821065

theorem tailTrace_394399 : CollatzResearch.WordTrace tailWord_394399 prefixEnd_394399 180014450357962351821065 := by
  unfold tailWord_394399
  simp only [CollatzResearch.WordTrace]
  refine ⟨14384913298167255831666251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9589942198778170554444167 14384913298167255831666251)
  ·
    refine ⟨21577369947250883747499377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14384913298167255831666251 21577369947250883747499377)
    ·
      refine ⟨16183027460438162810624533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21577369947250883747499377 16183027460438162810624533)
      ·
        refine ⟨758579412208038881748025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16183027460438162810624533 758579412208038881748025)
        ·
          refine ⟨568934559156029161311019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 758579412208038881748025 568934559156029161311019)
          ·
            refine ⟨853401838734043741966529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 568934559156029161311019 853401838734043741966529)
            ·
              refine ⟨640051379050532806474897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853401838734043741966529 640051379050532806474897)
              ·
                refine ⟨480038534287899604856173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640051379050532806474897 480038534287899604856173)
                ·
                  refine ⟨180014450357962351821065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480038534287899604856173 180014450357962351821065)
                  ·
                    rfl

theorem cell20_394399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 2, 3].length) (baseStart_394399 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394399 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394399 prefixEnd_394399 := by exact prefixLift 394399
  have htrace : WordTrace (prefixWord ++ tailWord_394399) baseStart_394399 baseEnd_394399 := by
    simpa [prefixWord, tailWord_394399, baseEnd_394399] using wordTrace_append hprefix tailTrace_394399
  have hstable : (prefixWord ++ tailWord_394399).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394399).length < 2 ^ (prefixWord ++ tailWord_394399).sum := by decide
  have hdescent : baseEnd_394399 < baseStart_394399 := by decide
  rcases family_descends (prefixWord ++ tailWord_394399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394465 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 4]
def baseStart_394465 : Nat := 118140960795 + 394465 * 2 ^ 59
def prefixEnd_394465 : Nat := 4983230072969 + 3 ^ 40 * 394465 * 2
def baseEnd_394465 : Nat := 180044574556359455620795

theorem tailTrace_394465 : CollatzResearch.WordTrace tailWord_394465 prefixEnd_394465 180044574556359455620795 := by
  unfold tailWord_394465
  simp only [CollatzResearch.WordTrace]
  refine ⟨14387320515928149103568849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9591547010618766069045899 14387320515928149103568849)
  ·
    refine ⟨10790490386946111827676637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14387320515928149103568849 10790490386946111827676637)
    ·
      refine ⟨4046433895104791935378739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10790490386946111827676637 4046433895104791935378739)
      ·
        refine ⟨6069650842657187903068109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046433895104791935378739 6069650842657187903068109)
        ·
          refine ⟨2276119065996445463650541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6069650842657187903068109 2276119065996445463650541)
          ·
            refine ⟨853544649748667048868953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2276119065996445463650541 853544649748667048868953)
            ·
              refine ⟨640158487311500286651715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853544649748667048868953 640158487311500286651715)
              ·
                refine ⟨960237730967250429977573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640158487311500286651715 960237730967250429977573)
                ·
                  refine ⟨180044574556359455620795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960237730967250429977573 180044574556359455620795)
                  ·
                    rfl

theorem cell20_394465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 4].length) (baseStart_394465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394465 prefixEnd_394465 := by exact prefixLift 394465
  have htrace : WordTrace (prefixWord ++ tailWord_394465) baseStart_394465 baseEnd_394465 := by
    simpa [prefixWord, tailWord_394465, baseEnd_394465] using wordTrace_append hprefix tailTrace_394465
  have hstable : (prefixWord ++ tailWord_394465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394465).length < 2 ^ (prefixWord ++ tailWord_394465).sum := by decide
  have hdescent : baseEnd_394465 < baseStart_394465 := by decide
  rcases family_descends (prefixWord ++ tailWord_394465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394510 : List Nat := [4, 1, 1, 2, 1, 5, 6]
def baseStart_394510 : Nat := 118140960795 + 394510 * 2 ^ 59
def prefixEnd_394510 : Nat := 4983230072969 + 3 ^ 40 * 394510 * 2
def baseEnd_394510 : Nat := 20007234864726588791179

theorem tailTrace_394510 : CollatzResearch.WordTrace tailWord_394510 prefixEnd_394510 20007234864726588791179 := by
  unfold tailWord_394510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798620225095640223619623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9592641200510081192637989 1798620225095640223619623)
  ·
    refine ⟨2697930337643460335429435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1798620225095640223619623 2697930337643460335429435)
    ·
      refine ⟨4046895506465190503144153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2697930337643460335429435 4046895506465190503144153)
      ·
        refine ⟨3035171629848892877358115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4046895506465190503144153 3035171629848892877358115)
        ·
          refine ⟨4552757444773339316037173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3035171629848892877358115 4552757444773339316037173)
          ·
            refine ⟨426821010447500560878485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4552757444773339316037173 426821010447500560878485)
            ·
              refine ⟨20007234864726588791179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 426821010447500560878485 20007234864726588791179)
              ·
                rfl

theorem cell20_394510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 5, 6].length) (baseStart_394510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394510 prefixEnd_394510 := by exact prefixLift 394510
  have htrace : WordTrace (prefixWord ++ tailWord_394510) baseStart_394510 baseEnd_394510 := by
    simpa [prefixWord, tailWord_394510, baseEnd_394510] using wordTrace_append hprefix tailTrace_394510
  have hstable : (prefixWord ++ tailWord_394510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394510).length < 2 ^ (prefixWord ++ tailWord_394510).sum := by decide
  have hdescent : baseEnd_394510 < baseStart_394510 := by decide
  rcases family_descends (prefixWord ++ tailWord_394510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394517 : List Nat := [1, 3, 2, 1, 2, 1, 1, 6, 3]
def baseStart_394517 : Nat := 118140960795 + 394517 * 2 ^ 59
def prefixEnd_394517 : Nat := 4983230072969 + 3 ^ 40 * 394517 * 2
def baseEnd_394517 : Nat := 180068308773278385887249

theorem tailTrace_394517 : CollatzResearch.WordTrace tailWord_394517 prefixEnd_394517 180068308773278385887249 := by
  unfold tailWord_394517
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389217111739761984461805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9592811407826507989641203 14389217111739761984461805)
  ·
    refine ⟨5395956416902410744173177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14389217111739761984461805 5395956416902410744173177)
    ·
      refine ⟨4046967312676808058129883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5395956416902410744173177 4046967312676808058129883)
      ·
        refine ⟨6070450969015212087194825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4046967312676808058129883 6070450969015212087194825)
        ·
          refine ⟨4552838226761409065396119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070450969015212087194825 4552838226761409065396119)
          ·
            refine ⟨6829257340142113598094179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4552838226761409065396119 6829257340142113598094179)
            ·
              refine ⟨10243886010213170397141269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6829257340142113598094179 10243886010213170397141269)
              ·
                refine ⟨480182156728742362365997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10243886010213170397141269 480182156728742362365997)
                ·
                  refine ⟨180068308773278385887249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480182156728742362365997 180068308773278385887249)
                  ·
                    rfl

theorem cell20_394517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 6, 3].length) (baseStart_394517 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394517 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394517 prefixEnd_394517 := by exact prefixLift 394517
  have htrace : WordTrace (prefixWord ++ tailWord_394517) baseStart_394517 baseEnd_394517 := by
    simpa [prefixWord, tailWord_394517, baseEnd_394517] using wordTrace_append hprefix tailTrace_394517
  have hstable : (prefixWord ++ tailWord_394517).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394517).length < 2 ^ (prefixWord ++ tailWord_394517).sum := by decide
  have hdescent : baseEnd_394517 < baseStart_394517 := by decide
  rcases family_descends (prefixWord ++ tailWord_394517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394526 : List Nat := [4, 3, 2, 1, 3, 1, 2, 1, 3]
def baseStart_394526 : Nat := 118140960795 + 394526 * 2 ^ 59
def prefixEnd_394526 : Nat := 4983230072969 + 3 ^ 40 * 394526 * 2
def baseEnd_394526 : Nat := 180072416618514354587213

theorem tailTrace_394526 : CollatzResearch.WordTrace tailWord_394526 prefixEnd_394526 180072416618514354587213 := by
  unfold tailWord_394526
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798693171088394565192429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9593030245804771014359621 1798693171088394565192429)
  ·
    refine ⟨674509939158147961947161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1798693171088394565192429 674509939158147961947161)
    ·
      refine ⟨505882454368610971460371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 674509939158147961947161 505882454368610971460371)
      ·
        refine ⟨758823681552916457190557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 505882454368610971460371 758823681552916457190557)
        ·
          refine ⟨284558880582343671446459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 758823681552916457190557 284558880582343671446459)
          ·
            refine ⟨426838320873515507169689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 284558880582343671446459 426838320873515507169689)
            ·
              refine ⟨320128740655136630377267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426838320873515507169689 320128740655136630377267)
              ·
                refine ⟨480193110982704945565901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320128740655136630377267 480193110982704945565901)
                ·
                  refine ⟨180072416618514354587213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480193110982704945565901 180072416618514354587213)
                  ·
                    rfl

theorem cell20_394526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 2, 1, 3].length) (baseStart_394526 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394526 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394526 prefixEnd_394526 := by exact prefixLift 394526
  have htrace : WordTrace (prefixWord ++ tailWord_394526) baseStart_394526 baseEnd_394526 := by
    simpa [prefixWord, tailWord_394526, baseEnd_394526] using wordTrace_append hprefix tailTrace_394526
  have hstable : (prefixWord ++ tailWord_394526).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394526).length < 2 ^ (prefixWord ++ tailWord_394526).sum := by decide
  have hdescent : baseEnd_394526 < baseStart_394526 := by decide
  rcases family_descends (prefixWord ++ tailWord_394526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394530 : List Nat := [3, 3, 1, 1, 4, 2, 2, 1, 3]
def baseStart_394530 : Nat := 118140960795 + 394530 * 2 ^ 59
def prefixEnd_394530 : Nat := 4983230072969 + 3 ^ 40 * 394530 * 2
def baseEnd_394530 : Nat := 180074242327508118453863

theorem tailTrace_394530 : CollatzResearch.WordTrace tailWord_394530 prefixEnd_394530 180074242327508118453863 := by
  unfold tailWord_394530
  simp only [CollatzResearch.WordTrace]
  refine ⟨3597422815173166301171261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9593127507128443469790029 3597422815173166301171261)
  ·
    refine ⟨1349033555689937362939223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3597422815173166301171261 1349033555689937362939223)
    ·
      refine ⟨2023550333534906044408835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349033555689937362939223 2023550333534906044408835)
      ·
        refine ⟨3035325500302359066613253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2023550333534906044408835 3035325500302359066613253)
        ·
          refine ⟨569123531306692324989985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3035325500302359066613253 569123531306692324989985)
          ·
            refine ⟨426842648480019243742489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569123531306692324989985 426842648480019243742489)
            ·
              refine ⟨320131986360014432806867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 426842648480019243742489 320131986360014432806867)
              ·
                refine ⟨480197979540021649210301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320131986360014432806867 480197979540021649210301)
                ·
                  refine ⟨180074242327508118453863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480197979540021649210301 180074242327508118453863)
                  ·
                    rfl

theorem cell20_394530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 2, 1, 3].length) (baseStart_394530 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394530 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394530 prefixEnd_394530 := by exact prefixLift 394530
  have htrace : WordTrace (prefixWord ++ tailWord_394530) baseStart_394530 baseEnd_394530 := by
    simpa [prefixWord, tailWord_394530, baseEnd_394530] using wordTrace_append hprefix tailTrace_394530
  have hstable : (prefixWord ++ tailWord_394530).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394530).length < 2 ^ (prefixWord ++ tailWord_394530).sum := by decide
  have hdescent : baseEnd_394530 < baseStart_394530 := by decide
  rcases family_descends (prefixWord ++ tailWord_394530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394531 : List Nat := [1, 1, 1, 4, 2, 3, 1, 7]
def baseStart_394531 : Nat := 118140960795 + 394531 * 2 ^ 59
def prefixEnd_394531 : Nat := 4983230072969 + 3 ^ 40 * 394531 * 2
def baseEnd_394531 : Nat := 60024899584918853140175

theorem tailTrace_394531 : CollatzResearch.WordTrace tailWord_394531 prefixEnd_394531 60024899584918853140175 := by
  unfold tailWord_394531
  simp only [CollatzResearch.WordTrace]
  refine ⟨14389727733689042375471447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9593151822459361583647631 14389727733689042375471447)
  ·
    refine ⟨21584591600533563563207171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14389727733689042375471447 21584591600533563563207171)
    ·
      refine ⟨32376887400800345344810757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21584591600533563563207171 32376887400800345344810757)
      ·
        refine ⟨6070666387650064752152017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 32376887400800345344810757 6070666387650064752152017)
        ·
          refine ⟨4552999790737548564114013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6070666387650064752152017 4552999790737548564114013)
          ·
            refine ⟨1707374921526580711542755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4552999790737548564114013 1707374921526580711542755)
            ·
              refine ⟨2561062382289871067314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1707374921526580711542755 2561062382289871067314133)
              ·
                refine ⟨60024899584918853140175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2561062382289871067314133 60024899584918853140175)
                ·
                  rfl

theorem cell20_394531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 7].length) (baseStart_394531 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394531 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394531 prefixEnd_394531 := by exact prefixLift 394531
  have htrace : WordTrace (prefixWord ++ tailWord_394531) baseStart_394531 baseEnd_394531 := by
    simpa [prefixWord, tailWord_394531, baseEnd_394531] using wordTrace_append hprefix tailTrace_394531
  have hstable : (prefixWord ++ tailWord_394531).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394531).length < 2 ^ (prefixWord ++ tailWord_394531).sum := by decide
  have hdescent : baseEnd_394531 < baseStart_394531 := by decide
  rcases family_descends (prefixWord ++ tailWord_394531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394548 : List Nat := [2, 5, 1, 1, 1, 1, 1, 8]
def baseStart_394548 : Nat := 118140960795 + 394548 * 2 ^ 59
def prefixEnd_394548 : Nat := 4983230072969 + 3 ^ 40 * 394548 * 2
def baseEnd_394548 : Nat := 60027486005993351951263

theorem tailTrace_394548 : CollatzResearch.WordTrace tailWord_394548 prefixEnd_394548 60027486005993351951263 := by
  unfold tailWord_394548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195173887313727139420149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9593565183084969519226865 7195173887313727139420149)
  ·
    refine ⟨674547551935661919320639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7195173887313727139420149 674547551935661919320639)
    ·
      refine ⟨1011821327903492878980959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 674547551935661919320639 1011821327903492878980959)
      ·
        refine ⟨1517731991855239318471439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011821327903492878980959 1517731991855239318471439)
        ·
          refine ⟨2276597987782858977707159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517731991855239318471439 2276597987782858977707159)
          ·
            refine ⟨3414896981674288466560739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276597987782858977707159 3414896981674288466560739)
            ·
              refine ⟨5122345472511432699841109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3414896981674288466560739 5122345472511432699841109)
              ·
                refine ⟨60027486005993351951263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5122345472511432699841109 60027486005993351951263)
                ·
                  rfl

theorem cell20_394548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 8].length) (baseStart_394548 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394548 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394548 prefixEnd_394548 := by exact prefixLift 394548
  have htrace : WordTrace (prefixWord ++ tailWord_394548) baseStart_394548 baseEnd_394548 := by
    simpa [prefixWord, tailWord_394548, baseEnd_394548] using wordTrace_append hprefix tailTrace_394548
  have hstable : (prefixWord ++ tailWord_394548).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394548).length < 2 ^ (prefixWord ++ tailWord_394548).sum := by decide
  have hdescent : baseEnd_394548 < baseStart_394548 := by decide
  rcases family_descends (prefixWord ++ tailWord_394548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394558 : List Nat := [4, 2, 1, 2, 1, 1, 2, 5, 2]
def baseStart_394558 : Nat := 118140960795 + 394558 * 2 ^ 59
def prefixEnd_394558 : Nat := 4983230072969 + 3 ^ 40 * 394558 * 2
def baseEnd_394558 : Nat := 180087022290464465520415

theorem tailTrace_394558 : CollatzResearch.WordTrace tailWord_394558 prefixEnd_394558 180087022290464465520415 := by
  unfold tailWord_394558
  simp only [CollatzResearch.WordTrace]
  refine ⟨1798839063073903248338041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9593808336394150657802885 1798839063073903248338041)
  ·
    refine ⟨1349129297305427436253531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1798839063073903248338041 1349129297305427436253531)
    ·
      refine ⟨2023693945958141154380297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1349129297305427436253531 2023693945958141154380297)
      ·
        refine ⟨1517770459468605865785223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2023693945958141154380297 1517770459468605865785223)
        ·
          refine ⟨2276655689202908798677835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1517770459468605865785223 2276655689202908798677835)
          ·
            refine ⟨3414983533804363198016753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2276655689202908798677835 3414983533804363198016753)
            ·
              refine ⟨2561237650353272398512565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3414983533804363198016753 2561237650353272398512565)
              ·
                refine ⟨240116029720619287360553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2561237650353272398512565 240116029720619287360553)
                ·
                  refine ⟨180087022290464465520415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240116029720619287360553 180087022290464465520415)
                  ·
                    rfl

theorem cell20_394558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 5, 2].length) (baseStart_394558 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394558 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394558 prefixEnd_394558 := by exact prefixLift 394558
  have htrace : WordTrace (prefixWord ++ tailWord_394558) baseStart_394558 baseEnd_394558 := by
    simpa [prefixWord, tailWord_394558, baseEnd_394558] using wordTrace_append hprefix tailTrace_394558
  have hstable : (prefixWord ++ tailWord_394558).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394558).length < 2 ^ (prefixWord ++ tailWord_394558).sum := by decide
  have hdescent : baseEnd_394558 < baseStart_394558 := by decide
  rcases family_descends (prefixWord ++ tailWord_394558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394572 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 3]
def baseStart_394572 : Nat := 118140960795 + 394572 * 2 ^ 59
def prefixEnd_394572 : Nat := 4983230072969 + 3 ^ 40 * 394572 * 2
def baseEnd_394572 : Nat := 180093412271942639053691

theorem tailTrace_394572 : CollatzResearch.WordTrace tailWord_394572 prefixEnd_394572 180093412271942639053691 := by
  unfold tailWord_394572
  simp only [CollatzResearch.WordTrace]
  refine ⟨7195611563270253188856985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9594148751027004251809313 7195611563270253188856985)
  ·
    refine ⟨5396708672452689891642739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7195611563270253188856985 5396708672452689891642739)
    ·
      refine ⟨8095063008679034837464109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5396708672452689891642739 8095063008679034837464109)
      ·
        refine ⟨3035648628254638064049041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8095063008679034837464109 3035648628254638064049041)
        ·
          refine ⟨2276736471190978548036781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3035648628254638064049041 2276736471190978548036781)
          ·
            refine ⟨853776176696616955513793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2276736471190978548036781 853776176696616955513793)
            ·
              refine ⟨640332132522462716635345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853776176696616955513793 640332132522462716635345)
              ·
                refine ⟨480249099391847037476509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640332132522462716635345 480249099391847037476509)
                ·
                  refine ⟨180093412271942639053691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480249099391847037476509 180093412271942639053691)
                  ·
                    rfl

theorem cell20_394572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3].length) (baseStart_394572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394572 prefixEnd_394572 := by exact prefixLift 394572
  have htrace : WordTrace (prefixWord ++ tailWord_394572) baseStart_394572 baseEnd_394572 := by
    simpa [prefixWord, tailWord_394572, baseEnd_394572] using wordTrace_append hprefix tailTrace_394572
  have hstable : (prefixWord ++ tailWord_394572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394572).length < 2 ^ (prefixWord ++ tailWord_394572).sum := by decide
  have hdescent : baseEnd_394572 < baseStart_394572 := by decide
  rcases family_descends (prefixWord ++ tailWord_394572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394579 : List Nat := [1, 1, 1, 2, 1, 1, 7, 4, 2]
def baseStart_394579 : Nat := 118140960795 + 394579 * 2 ^ 59
def prefixEnd_394579 : Nat := 4983230072969 + 3 ^ 40 * 394579 * 2
def baseEnd_394579 : Nat := 180096607262681725820329

theorem tailTrace_394579 : CollatzResearch.WordTrace tailWord_394579 prefixEnd_394579 180096607262681725820329 := by
  unfold tailWord_394579
  simp only [CollatzResearch.WordTrace]
  refine ⟨14391478437515146573218791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9594318958343431048812527 14391478437515146573218791)
  ·
    refine ⟨21587217656272719859828187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14391478437515146573218791 21587217656272719859828187)
    ·
      refine ⟨32380826484409079789742281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21587217656272719859828187 32380826484409079789742281)
      ·
        refine ⟨24285619863306809842306711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32380826484409079789742281 24285619863306809842306711)
        ·
          refine ⟨36428429794960214763460067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24285619863306809842306711 36428429794960214763460067)
          ·
            refine ⟨54642644692440322145190101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 36428429794960214763460067 54642644692440322145190101)
            ·
              refine ⟨1280686984979070050277893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 54642644692440322145190101 1280686984979070050277893)
              ·
                refine ⟨240128809683575634427105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1280686984979070050277893 240128809683575634427105)
                ·
                  refine ⟨180096607262681725820329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240128809683575634427105 180096607262681725820329)
                  ·
                    rfl

theorem cell20_394579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 4, 2].length) (baseStart_394579 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394579 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394579 prefixEnd_394579 := by exact prefixLift 394579
  have htrace : WordTrace (prefixWord ++ tailWord_394579) baseStart_394579 baseEnd_394579 := by
    simpa [prefixWord, tailWord_394579, baseEnd_394579] using wordTrace_append hprefix tailTrace_394579
  have hstable : (prefixWord ++ tailWord_394579).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394579).length < 2 ^ (prefixWord ++ tailWord_394579).sum := by decide
  have hdescent : baseEnd_394579 < baseStart_394579 := by decide
  rcases family_descends (prefixWord ++ tailWord_394579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394613 : List Nat := [1, 3, 4, 1, 3, 1, 2, 3, 2]
def baseStart_394613 : Nat := 118140960795 + 394613 * 2 ^ 59
def prefixEnd_394613 : Nat := 4983230072969 + 3 ^ 40 * 394613 * 2
def baseEnd_394613 : Nat := 180112125789128718686857

theorem tailTrace_394613 : CollatzResearch.WordTrace tailWord_394613 prefixEnd_394613 180112125789128718686857 := by
  unfold tailWord_394613
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392718519391970379956493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9595145679594646919970995 14392718519391970379956493)
  ·
    refine ⟨5397269444771988892483685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14392718519391970379956493 5397269444771988892483685)
    ·
      refine ⟨1011988020894747917340691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5397269444771988892483685 1011988020894747917340691)
      ·
        refine ⟨1517982031342121876011037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1011988020894747917340691 1517982031342121876011037)
        ·
          refine ⟨569243261753295703504139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1517982031342121876011037 569243261753295703504139)
          ·
            refine ⟨853864892629943555256209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569243261753295703504139 853864892629943555256209)
            ·
              refine ⟨640398669472457666442157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 853864892629943555256209 640398669472457666442157)
              ·
                refine ⟨240149501052171624915809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 640398669472457666442157 240149501052171624915809)
                ·
                  refine ⟨180112125789128718686857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240149501052171624915809 180112125789128718686857)
                  ·
                    rfl

theorem cell20_394613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 1, 2, 3, 2].length) (baseStart_394613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394613 prefixEnd_394613 := by exact prefixLift 394613
  have htrace : WordTrace (prefixWord ++ tailWord_394613) baseStart_394613 baseEnd_394613 := by
    simpa [prefixWord, tailWord_394613, baseEnd_394613] using wordTrace_append hprefix tailTrace_394613
  have hstable : (prefixWord ++ tailWord_394613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394613).length < 2 ^ (prefixWord ++ tailWord_394613).sum := by decide
  have hdescent : baseEnd_394613 < baseStart_394613 := by decide
  rcases family_descends (prefixWord ++ tailWord_394613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394617 : List Nat := [1, 2, 1, 3, 2, 1, 3, 5, 2]
def baseStart_394617 : Nat := 118140960795 + 394617 * 2 ^ 59
def prefixEnd_394617 : Nat := 4983230072969 + 3 ^ 40 * 394617 * 2
def baseEnd_394617 : Nat := 180113951498122482553507

theorem tailTrace_394617 : CollatzResearch.WordTrace tailWord_394617 prefixEnd_394617 180113951498122482553507 := by
  unfold tailWord_394617
  simp only [CollatzResearch.WordTrace]
  refine ⟨14392864411377479063102105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9595242940918319375401403 14392864411377479063102105)
  ·
    refine ⟨10794648308533109297326579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14392864411377479063102105 10794648308533109297326579)
    ·
      refine ⟨16191972462799663945989869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10794648308533109297326579 16191972462799663945989869)
      ·
        refine ⟨6071989673549873979746201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16191972462799663945989869 6071989673549873979746201)
        ·
          refine ⟨4553992255162405484809651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6071989673549873979746201 4553992255162405484809651)
          ·
            refine ⟨6830988382743608227214477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4553992255162405484809651 6830988382743608227214477)
            ·
              refine ⟨2561620643528853085205429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6830988382743608227214477 2561620643528853085205429)
              ·
                refine ⟨240151935330829976738009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2561620643528853085205429 240151935330829976738009)
                ·
                  refine ⟨180113951498122482553507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240151935330829976738009 180113951498122482553507)
                  ·
                    rfl

theorem cell20_394617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2].length) (baseStart_394617 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394617 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394617 prefixEnd_394617 := by exact prefixLift 394617
  have htrace : WordTrace (prefixWord ++ tailWord_394617) baseStart_394617 baseEnd_394617 := by
    simpa [prefixWord, tailWord_394617, baseEnd_394617] using wordTrace_append hprefix tailTrace_394617
  have hstable : (prefixWord ++ tailWord_394617).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394617).length < 2 ^ (prefixWord ++ tailWord_394617).sum := by decide
  have hdescent : baseEnd_394617 < baseStart_394617 := by decide
  rcases family_descends (prefixWord ++ tailWord_394617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394631 : List Nat := [1, 1, 4, 2, 2, 3, 1, 1, 5]
def baseStart_394631 : Nat := 118140960795 + 394631 * 2 ^ 59
def prefixEnd_394631 : Nat := 4983230072969 + 3 ^ 40 * 394631 * 2
def baseEnd_394631 : Nat := 180120341479600656086783

theorem tailTrace_394631 : CollatzResearch.WordTrace tailWord_394631 prefixEnd_394631 180120341479600656086783 := by
  unfold tailWord_394631
  simp only [CollatzResearch.WordTrace]
  refine ⟨14393375033326759454111747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9595583355551172969407831 14393375033326759454111747)
  ·
    refine ⟨21590062549990139181167621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14393375033326759454111747 21590062549990139181167621)
    ·
      refine ⟨4048136728123151096468929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21590062549990139181167621 4048136728123151096468929)
      ·
        refine ⟨3036102546092363322351697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4048136728123151096468929 3036102546092363322351697)
        ·
          refine ⟨2277076909569272491763773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3036102546092363322351697 2277076909569272491763773)
          ·
            refine ⟨853903841088477184411415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2277076909569272491763773 853903841088477184411415)
            ·
              refine ⟨1280855761632715776617123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 853903841088477184411415 1280855761632715776617123)
              ·
                refine ⟨1921283642449073664925685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1280855761632715776617123 1921283642449073664925685)
                ·
                  refine ⟨180120341479600656086783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1921283642449073664925685 180120341479600656086783)
                  ·
                    rfl

theorem cell20_394631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 1, 1, 5].length) (baseStart_394631 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394631 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394631 prefixEnd_394631 := by exact prefixLift 394631
  have htrace : WordTrace (prefixWord ++ tailWord_394631) baseStart_394631 baseEnd_394631 := by
    simpa [prefixWord, tailWord_394631, baseEnd_394631] using wordTrace_append hprefix tailTrace_394631
  have hstable : (prefixWord ++ tailWord_394631).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394631).length < 2 ^ (prefixWord ++ tailWord_394631).sum := by decide
  have hdescent : baseEnd_394631 < baseStart_394631 := by decide
  rcases family_descends (prefixWord ++ tailWord_394631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394700 : List Nat := [2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_394700 : Nat := 118140960795 + 394700 * 2 ^ 59
def prefixEnd_394700 : Nat := 4983230072969 + 3 ^ 40 * 394700 * 2
def baseEnd_394700 : Nat := 60050611653247694262167

theorem tailTrace_394700 : CollatzResearch.WordTrace tailWord_394700 prefixEnd_394700 60050611653247694262167 := by
  unfold tailWord_394700
  simp only [CollatzResearch.WordTrace]
  refine ⟨7197945835038392119186777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9597261113384522825582369 7197945835038392119186777)
  ·
    refine ⟨5398459376278794089390083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7197945835038392119186777 5398459376278794089390083)
    ·
      refine ⟨8097689064418191134085125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5398459376278794089390083 8097689064418191134085125)
      ·
        refine ⟨1518316699578410837640961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8097689064418191134085125 1518316699578410837640961)
        ·
          refine ⟨1138737524683808128230721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1518316699578410837640961 1138737524683808128230721)
          ·
            refine ⟨854053143512856096173041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138737524683808128230721 854053143512856096173041)
            ·
              refine ⟨640539857634642072129781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854053143512856096173041 640539857634642072129781)
              ·
                refine ⟨60050611653247694262167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640539857634642072129781 60050611653247694262167)
                ·
                  rfl

theorem cell20_394700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_394700 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394700 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394700 prefixEnd_394700 := by exact prefixLift 394700
  have htrace : WordTrace (prefixWord ++ tailWord_394700) baseStart_394700 baseEnd_394700 := by
    simpa [prefixWord, tailWord_394700, baseEnd_394700] using wordTrace_append hprefix tailTrace_394700
  have hstable : (prefixWord ++ tailWord_394700).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394700).length < 2 ^ (prefixWord ++ tailWord_394700).sum := by decide
  have hdescent : baseEnd_394700 < baseStart_394700 := by decide
  rcases family_descends (prefixWord ++ tailWord_394700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394721 : List Nat := [1, 2, 3, 1, 2, 3, 2, 6]
def baseStart_394721 : Nat := 118140960795 + 394721 * 2 ^ 59
def prefixEnd_394721 : Nat := 4983230072969 + 3 ^ 40 * 394721 * 2
def baseEnd_394721 : Nat := 60053806643986781028805

theorem tailTrace_394721 : CollatzResearch.WordTrace tailWord_394721 prefixEnd_394721 60053806643986781028805 := by
  unfold tailWord_394721
  simp only [CollatzResearch.WordTrace]
  refine ⟨14396657603000704824888017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9597771735333803216592011 14396657603000704824888017)
  ·
    refine ⟨10797493202250528618666013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14396657603000704824888017 10797493202250528618666013)
    ·
      refine ⟨4049059950843948231999755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10797493202250528618666013 4049059950843948231999755)
      ·
        refine ⟨6073589926265922347999633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049059950843948231999755 6073589926265922347999633)
        ·
          refine ⟨4555192444699441760999725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6073589926265922347999633 4555192444699441760999725)
          ·
            refine ⟨1708197166762290660374897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4555192444699441760999725 1708197166762290660374897)
            ·
              refine ⟨1281147875071717995281173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708197166762290660374897 1281147875071717995281173)
              ·
                refine ⟨60053806643986781028805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1281147875071717995281173 60053806643986781028805)
                ·
                  rfl

theorem cell20_394721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 3, 2, 6].length) (baseStart_394721 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394721 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394721 prefixEnd_394721 := by exact prefixLift 394721
  have htrace : WordTrace (prefixWord ++ tailWord_394721) baseStart_394721 baseEnd_394721 := by
    simpa [prefixWord, tailWord_394721, baseEnd_394721] using wordTrace_append hprefix tailTrace_394721
  have hstable : (prefixWord ++ tailWord_394721).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394721).length < 2 ^ (prefixWord ++ tailWord_394721).sum := by decide
  have hdescent : baseEnd_394721 < baseStart_394721 := by decide
  rcases family_descends (prefixWord ++ tailWord_394721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394741 : List Nat := [1, 3, 5, 1, 1, 2, 2, 2, 3]
def baseStart_394741 : Nat := 118140960795 + 394741 * 2 ^ 59
def prefixEnd_394741 : Nat := 4983230072969 + 3 ^ 40 * 394741 * 2
def baseEnd_394741 : Nat := 180170548476929162419667

theorem tailTrace_394741 : CollatzResearch.WordTrace tailWord_394741 prefixEnd_394741 180170548476929162419667 := by
  unfold tailWord_394741
  simp only [CollatzResearch.WordTrace]
  refine ⟨14397387062928248240616077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9598258041952165493744051 14397387062928248240616077)
  ·
    refine ⟨5399020148598093090231029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14397387062928248240616077 5399020148598093090231029)
    ·
      refine ⟨506158138931071227209159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5399020148598093090231029 506158138931071227209159)
      ·
        refine ⟨759237208396606840813739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506158138931071227209159 759237208396606840813739)
        ·
          refine ⟨1138855812594910261220609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 759237208396606840813739 1138855812594910261220609)
          ·
            refine ⟨854141859446182695915457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1138855812594910261220609 854141859446182695915457)
            ·
              refine ⟨640606394584637021936593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854141859446182695915457 640606394584637021936593)
              ·
                refine ⟨480454795938477766452445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 640606394584637021936593 480454795938477766452445)
                ·
                  refine ⟨180170548476929162419667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480454795938477766452445 180170548476929162419667)
                  ·
                    rfl

theorem cell20_394741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 2, 2, 3].length) (baseStart_394741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394741 prefixEnd_394741 := by exact prefixLift 394741
  have htrace : WordTrace (prefixWord ++ tailWord_394741) baseStart_394741 baseEnd_394741 := by
    simpa [prefixWord, tailWord_394741, baseEnd_394741] using wordTrace_append hprefix tailTrace_394741
  have hstable : (prefixWord ++ tailWord_394741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394741).length < 2 ^ (prefixWord ++ tailWord_394741).sum := by decide
  have hdescent : baseEnd_394741 < baseStart_394741 := by decide
  rcases family_descends (prefixWord ++ tailWord_394741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394748 : List Nat := [2, 2, 2, 1, 2, 1, 6, 2, 2]
def baseStart_394748 : Nat := 118140960795 + 394748 * 2 ^ 59
def prefixEnd_394748 : Nat := 4983230072969 + 3 ^ 40 * 394748 * 2
def baseEnd_394748 : Nat := 180173743467668249186305

theorem tailTrace_394748 : CollatzResearch.WordTrace tailWord_394748 prefixEnd_394748 180173743467668249186305 := by
  unfold tailWord_394748
  simp only [CollatzResearch.WordTrace]
  refine ⟨7198821186951444218060449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9598428249268592290747265 7198821186951444218060449)
  ·
    refine ⟨5399115890213583163545337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7198821186951444218060449 5399115890213583163545337)
    ·
      refine ⟨4049336917660187372659003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5399115890213583163545337 4049336917660187372659003)
      ·
        refine ⟨6074005376490281058988505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4049336917660187372659003 6074005376490281058988505)
        ·
          refine ⟨4555504032367710794241379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6074005376490281058988505 4555504032367710794241379)
          ·
            refine ⟨6833256048551566191362069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4555504032367710794241379 6833256048551566191362069)
            ·
              refine ⟨320308877275854665220097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6833256048551566191362069 320308877275854665220097)
              ·
                refine ⟨240231657956890998915073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320308877275854665220097 240231657956890998915073)
                ·
                  refine ⟨180173743467668249186305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240231657956890998915073 180173743467668249186305)
                  ·
                    rfl

theorem cell20_394748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 6, 2, 2].length) (baseStart_394748 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394748 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394748 prefixEnd_394748 := by exact prefixLift 394748
  have htrace : WordTrace (prefixWord ++ tailWord_394748) baseStart_394748 baseEnd_394748 := by
    simpa [prefixWord, tailWord_394748, baseEnd_394748] using wordTrace_append hprefix tailTrace_394748
  have hstable : (prefixWord ++ tailWord_394748).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394748).length < 2 ^ (prefixWord ++ tailWord_394748).sum := by decide
  have hdescent : baseEnd_394748 < baseStart_394748 := by decide
  rcases family_descends (prefixWord ++ tailWord_394748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394765 : List Nat := [1, 7, 1, 1, 2, 1, 1, 2, 4]
def baseStart_394765 : Nat := 118140960795 + 394765 * 2 ^ 59
def prefixEnd_394765 : Nat := 4983230072969 + 3 ^ 40 * 394765 * 2
def baseEnd_394765 : Nat := 180181502730891745619569

theorem tailTrace_394765 : CollatzResearch.WordTrace tailWord_394765 prefixEnd_394765 180181502730891745619569 := by
  unfold tailWord_394765
  simp only [CollatzResearch.WordTrace]
  refine ⟨14398262414841300339489749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9598841609894200226326499 14398262414841300339489749)
  ·
    refine ⟨337459275347842976706791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 14398262414841300339489749 337459275347842976706791)
    ·
      refine ⟨506188913021764465060187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 337459275347842976706791 506188913021764465060187)
      ·
        refine ⟨759283369532646697590281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506188913021764465060187 759283369532646697590281)
        ·
          refine ⟨569462527149485023192711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759283369532646697590281 569462527149485023192711)
          ·
            refine ⟨854193790724227534789067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569462527149485023192711 854193790724227534789067)
            ·
              refine ⟨1281290686086341302183601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 854193790724227534789067 1281290686086341302183601)
              ·
                refine ⟨960968014564755976637701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281290686086341302183601 960968014564755976637701)
                ·
                  refine ⟨180181502730891745619569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 960968014564755976637701 180181502730891745619569)
                  ·
                    rfl

theorem cell20_394765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 1, 1, 2, 4].length) (baseStart_394765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394765 prefixEnd_394765 := by exact prefixLift 394765
  have htrace : WordTrace (prefixWord ++ tailWord_394765) baseStart_394765 baseEnd_394765 := by
    simpa [prefixWord, tailWord_394765, baseEnd_394765] using wordTrace_append hprefix tailTrace_394765
  have hstable : (prefixWord ++ tailWord_394765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394765).length < 2 ^ (prefixWord ++ tailWord_394765).sum := by decide
  have hdescent : baseEnd_394765 < baseStart_394765 := by decide
  rcases family_descends (prefixWord ++ tailWord_394765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394772 : List Nat := [2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_394772 : Nat := 118140960795 + 394772 * 2 ^ 59
def prefixEnd_394772 : Nat := 4983230072969 + 3 ^ 40 * 394772 * 2
def baseEnd_394772 : Nat := 60061565907210277462069

theorem tailTrace_394772 : CollatzResearch.WordTrace tailWord_394772 prefixEnd_394772 60061565907210277462069 := by
  unfold tailWord_394772
  simp only [CollatzResearch.WordTrace]
  refine ⟨7199258862907970267497285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9599011817210627023329713 7199258862907970267497285)
  ·
    refine ⟨1349861036795244425155741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7199258862907970267497285 1349861036795244425155741)
    ·
      refine ⟨506197888798216659433403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1349861036795244425155741 506197888798216659433403)
      ·
        refine ⟨759296833197324989150105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 506197888798216659433403 759296833197324989150105)
        ·
          refine ⟨569472624897993741862579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 759296833197324989150105 569472624897993741862579)
          ·
            refine ⟨854208937346990612793869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569472624897993741862579 854208937346990612793869)
            ·
              refine ⟨320328351505121479797701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 854208937346990612793869 320328351505121479797701)
              ·
                refine ⟨60061565907210277462069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320328351505121479797701 60061565907210277462069)
                ·
                  rfl

theorem cell20_394772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_394772 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394772 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394772 prefixEnd_394772 := by exact prefixLift 394772
  have htrace : WordTrace (prefixWord ++ tailWord_394772) baseStart_394772 baseEnd_394772 := by
    simpa [prefixWord, tailWord_394772, baseEnd_394772] using wordTrace_append hprefix tailTrace_394772
  have hstable : (prefixWord ++ tailWord_394772).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394772).length < 2 ^ (prefixWord ++ tailWord_394772).sum := by decide
  have hdescent : baseEnd_394772 < baseStart_394772 := by decide
  rcases family_descends (prefixWord ++ tailWord_394772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394807 : List Nat := [1, 1, 3, 1, 2, 4, 2, 4, 2]
def baseStart_394807 : Nat := 118140960795 + 394807 * 2 ^ 59
def prefixEnd_394807 : Nat := 4983230072969 + 3 ^ 40 * 394807 * 2
def baseEnd_394807 : Nat := 180200672675326266219397

theorem tailTrace_394807 : CollatzResearch.WordTrace tailWord_394807 prefixEnd_394807 180200672675326266219397 := by
  unfold tailWord_394807
  simp only [CollatzResearch.WordTrace]
  refine ⟨14399794280689141512518675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9599862853792761008345783 14399794280689141512518675)
  ·
    refine ⟨21599691421033712268778013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14399794280689141512518675 21599691421033712268778013)
    ·
      refine ⟨8099884282887642100791755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21599691421033712268778013 8099884282887642100791755)
      ·
        refine ⟨12149826424331463151187633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8099884282887642100791755 12149826424331463151187633)
        ·
          refine ⟨9112369818248597363390725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12149826424331463151187633 9112369818248597363390725)
          ·
            refine ⟨1708569340921612005635761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9112369818248597363390725 1708569340921612005635761)
            ·
              refine ⟨1281427005691209004226821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708569340921612005635761 1281427005691209004226821)
              ·
                refine ⟨240267563567101688292529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1281427005691209004226821 240267563567101688292529)
                ·
                  refine ⟨180200672675326266219397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240267563567101688292529 180200672675326266219397)
                  ·
                    rfl

theorem cell20_394807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 4, 2].length) (baseStart_394807 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394807 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394807 prefixEnd_394807 := by exact prefixLift 394807
  have htrace : WordTrace (prefixWord ++ tailWord_394807) baseStart_394807 baseEnd_394807 := by
    simpa [prefixWord, tailWord_394807, baseEnd_394807] using wordTrace_append hprefix tailTrace_394807
  have hstable : (prefixWord ++ tailWord_394807).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394807).length < 2 ^ (prefixWord ++ tailWord_394807).sum := by decide
  have hdescent : baseEnd_394807 < baseStart_394807 := by decide
  rcases family_descends (prefixWord ++ tailWord_394807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394828 : List Nat := [2, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_394828 : Nat := 118140960795 + 394828 * 2 ^ 59
def prefixEnd_394828 : Nat := 4983230072969 + 3 ^ 40 * 394828 * 2
def baseEnd_394828 : Nat := 180210257647543526519311

theorem tailTrace_394828 : CollatzResearch.WordTrace tailWord_394828 prefixEnd_394828 180210257647543526519311 := by
  unfold tailWord_394828
  simp only [CollatzResearch.WordTrace]
  refine ⟨7200280106806531049516569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9600373475742041399355425 7200280106806531049516569)
  ·
    refine ⟨5400210080104898287137427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7200280106806531049516569 5400210080104898287137427)
    ·
      refine ⟨8100315120157347430706141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5400210080104898287137427 8100315120157347430706141)
      ·
        refine ⟨3037618170059005286514803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8100315120157347430706141 3037618170059005286514803)
        ·
          refine ⟨4556427255088507929772205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3037618170059005286514803 4556427255088507929772205)
          ·
            refine ⟨1708660220658190473664577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4556427255088507929772205 1708660220658190473664577)
            ·
              refine ⟨1281495165493642855248433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1708660220658190473664577 1281495165493642855248433)
              ·
                refine ⟨961121374120232141436325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1281495165493642855248433 961121374120232141436325)
                ·
                  refine ⟨180210257647543526519311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961121374120232141436325 180210257647543526519311)
                  ·
                    rfl

theorem cell20_394828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_394828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394828 prefixEnd_394828 := by exact prefixLift 394828
  have htrace : WordTrace (prefixWord ++ tailWord_394828) baseStart_394828 baseEnd_394828 := by
    simpa [prefixWord, tailWord_394828, baseEnd_394828] using wordTrace_append hprefix tailTrace_394828
  have hstable : (prefixWord ++ tailWord_394828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394828).length < 2 ^ (prefixWord ++ tailWord_394828).sum := by decide
  have hdescent : baseEnd_394828 < baseStart_394828 := by decide
  rcases family_descends (prefixWord ++ tailWord_394828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394862 : List Nat := [4, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_394862 : Nat := 118140960795 + 394862 * 2 ^ 59
def prefixEnd_394862 : Nat := 4983230072969 + 3 ^ 40 * 394862 * 2
def baseEnd_394862 : Nat := 180225776173990519385839

theorem tailTrace_394862 : CollatzResearch.WordTrace tailWord_394862 prefixEnd_394862 180225776173990519385839 := by
  unfold tailWord_394862
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800225036936235738221355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9601200196993257270513893 1800225036936235738221355)
  ·
    refine ⟨2700337555404353607332033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800225036936235738221355 2700337555404353607332033)
    ·
      refine ⟨2025253166553265205499025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2700337555404353607332033 2025253166553265205499025)
      ·
        refine ⟨1518939874914948904124269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2025253166553265205499025 1518939874914948904124269)
        ·
          refine ⟨569602453093105839046601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1518939874914948904124269 569602453093105839046601)
          ·
            refine ⟨427201839819829379284951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 569602453093105839046601 427201839819829379284951)
            ·
              refine ⟨640802759729744068927427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427201839819829379284951 640802759729744068927427)
              ·
                refine ⟨961204139594616103391141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640802759729744068927427 961204139594616103391141)
                ·
                  refine ⟨180225776173990519385839, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961204139594616103391141 180225776173990519385839)
                  ·
                    rfl

theorem cell20_394862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_394862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394862 prefixEnd_394862 := by exact prefixLift 394862
  have htrace : WordTrace (prefixWord ++ tailWord_394862) baseStart_394862 baseEnd_394862 := by
    simpa [prefixWord, tailWord_394862, baseEnd_394862] using wordTrace_append hprefix tailTrace_394862
  have hstable : (prefixWord ++ tailWord_394862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394862).length < 2 ^ (prefixWord ++ tailWord_394862).sum := by decide
  have hdescent : baseEnd_394862 < baseStart_394862 := by decide
  rcases family_descends (prefixWord ++ tailWord_394862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394873 : List Nat := [1, 2, 1, 3, 3, 1, 4, 5]
def baseStart_394873 : Nat := 118140960795 + 394873 * 2 ^ 59
def prefixEnd_394873 : Nat := 4983230072969 + 3 ^ 40 * 394873 * 2
def baseEnd_394873 : Nat := 60076932291241123339709

theorem tailTrace_394873 : CollatzResearch.WordTrace tailWord_394873 prefixEnd_394873 60076932291241123339709 := by
  unfold tailWord_394873
  simp only [CollatzResearch.WordTrace]
  refine ⟨14402201498450034784421273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9601467665633356522947515 14402201498450034784421273)
  ·
    refine ⟨10801651123837526088315955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14402201498450034784421273 10801651123837526088315955)
    ·
      refine ⟨16202476685756289132473933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10801651123837526088315955 16202476685756289132473933)
      ·
        refine ⟨6075928757158608424677725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16202476685756289132473933 6075928757158608424677725)
        ·
          refine ⟨2278473283934478159254147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6075928757158608424677725 2278473283934478159254147)
          ·
            refine ⟨3417709925901717238881221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2278473283934478159254147 3417709925901717238881221)
            ·
              refine ⟨640820611106571982290229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3417709925901717238881221 640820611106571982290229)
              ·
                refine ⟨60076932291241123339709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 640820611106571982290229 60076932291241123339709)
                ·
                  rfl

theorem cell20_394873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 4, 5].length) (baseStart_394873 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394873 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394873 prefixEnd_394873 := by exact prefixLift 394873
  have htrace : WordTrace (prefixWord ++ tailWord_394873) baseStart_394873 baseEnd_394873 := by
    simpa [prefixWord, tailWord_394873, baseEnd_394873] using wordTrace_append hprefix tailTrace_394873
  have hstable : (prefixWord ++ tailWord_394873).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394873).length < 2 ^ (prefixWord ++ tailWord_394873).sum := by decide
  have hdescent : baseEnd_394873 < baseStart_394873 := by decide
  rcases family_descends (prefixWord ++ tailWord_394873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394911 : List Nat := [1, 1, 2, 7, 9]
def baseStart_394911 : Nat := 118140960795 + 394911 * 2 ^ 59
def prefixEnd_394911 : Nat := 4983230072969 + 3 ^ 40 * 394911 * 2
def baseEnd_394911 : Nat := 2225285692705729959905

theorem tailTrace_394911 : CollatzResearch.WordTrace tailWord_394911 prefixEnd_394911 2225285692705729959905 := by
  unfold tailWord_394911
  simp only [CollatzResearch.WordTrace]
  refine ⟨14403587472312367274304587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9602391648208244849536391 14403587472312367274304587)
  ·
    refine ⟨21605381208468550911456881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14403587472312367274304587 21605381208468550911456881)
    ·
      refine ⟨16204035906351413183592661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21605381208468550911456881 16204035906351413183592661)
      ·
        refine ⟨379782091555111246490453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 16204035906351413183592661 379782091555111246490453)
        ·
          refine ⟨2225285692705729959905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 9 379782091555111246490453 2225285692705729959905)
          ·
            rfl

theorem cell20_394911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 9].length) (baseStart_394911 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394911 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394911 prefixEnd_394911 := by exact prefixLift 394911
  have htrace : WordTrace (prefixWord ++ tailWord_394911) baseStart_394911 baseEnd_394911 := by
    simpa [prefixWord, tailWord_394911, baseEnd_394911] using wordTrace_append hprefix tailTrace_394911
  have hstable : (prefixWord ++ tailWord_394911).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394911).length < 2 ^ (prefixWord ++ tailWord_394911).sum := by decide
  have hdescent : baseEnd_394911 < baseStart_394911 := by decide
  rcases family_descends (prefixWord ++ tailWord_394911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394935 : List Nat := [1, 1, 3, 1, 5, 1, 2, 3, 3]
def baseStart_394935 : Nat := 118140960795 + 394935 * 2 ^ 59
def prefixEnd_394935 : Nat := 4983230072969 + 3 ^ 40 * 394935 * 2
def baseEnd_394935 : Nat := 180259095363126709952207

theorem tailTrace_394935 : CollatzResearch.WordTrace tailWord_394935 prefixEnd_394935 180259095363126709952207 := by
  unfold tailWord_394935
  simp only [CollatzResearch.WordTrace]
  refine ⟨14404462824225419373178259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9602975216150279582118839 14404462824225419373178259)
  ·
    refine ⟨21606694236338129059767389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14404462824225419373178259 21606694236338129059767389)
    ·
      refine ⟨8102510338626798397412771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 21606694236338129059767389 8102510338626798397412771)
      ·
        refine ⟨12153765507940197596119157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8102510338626798397412771 12153765507940197596119157)
        ·
          refine ⟨1139415516369393524636171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12153765507940197596119157 1139415516369393524636171)
          ·
            refine ⟨1709123274554090286954257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1139415516369393524636171 1709123274554090286954257)
            ·
              refine ⟨1281842455915567715215693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1709123274554090286954257 1281842455915567715215693)
              ·
                refine ⟨480690920968337893205885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1281842455915567715215693 480690920968337893205885)
                ·
                  refine ⟨180259095363126709952207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480690920968337893205885 180259095363126709952207)
                  ·
                    rfl

theorem cell20_394935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_394935 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394935 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394935 prefixEnd_394935 := by exact prefixLift 394935
  have htrace : WordTrace (prefixWord ++ tailWord_394935) baseStart_394935 baseEnd_394935 := by
    simpa [prefixWord, tailWord_394935, baseEnd_394935] using wordTrace_append hprefix tailTrace_394935
  have hstable : (prefixWord ++ tailWord_394935).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394935).length < 2 ^ (prefixWord ++ tailWord_394935).sum := by decide
  have hdescent : baseEnd_394935 < baseStart_394935 := by decide
  rcases family_descends (prefixWord ++ tailWord_394935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394942 : List Nat := [4, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_394942 : Nat := 118140960795 + 394942 * 2 ^ 59
def prefixEnd_394942 : Nat := 4983230072969 + 3 ^ 40 * 394942 * 2
def baseEnd_394942 : Nat := 180262290353865796718845

theorem tailTrace_394942 : CollatzResearch.WordTrace tailWord_394942 prefixEnd_394942 180262290353865796718845 := by
  unfold tailWord_394942
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800589766900007446085385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9603145423466706379122053 1800589766900007446085385)
  ·
    refine ⟨1350442325175005584564039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1800589766900007446085385 1350442325175005584564039)
    ·
      refine ⟨2025663487762508376846059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1350442325175005584564039 2025663487762508376846059)
      ·
        refine ⟨3038495231643762565269089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025663487762508376846059 3038495231643762565269089)
        ·
          refine ⟨2278871423732821923951817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3038495231643762565269089 2278871423732821923951817)
          ·
            refine ⟨1709153567799616442963863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2278871423732821923951817 1709153567799616442963863)
            ·
              refine ⟨2563730351699424664445795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1709153567799616442963863 2563730351699424664445795)
              ·
                refine ⟨3845595527549136996668693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2563730351699424664445795 3845595527549136996668693)
                ·
                  refine ⟨180262290353865796718845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3845595527549136996668693 180262290353865796718845)
                  ·
                    rfl

theorem cell20_394942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_394942 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394942 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394942 prefixEnd_394942 := by exact prefixLift 394942
  have htrace : WordTrace (prefixWord ++ tailWord_394942) baseStart_394942 baseEnd_394942 := by
    simpa [prefixWord, tailWord_394942, baseEnd_394942] using wordTrace_append hprefix tailTrace_394942
  have hstable : (prefixWord ++ tailWord_394942).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394942).length < 2 ^ (prefixWord ++ tailWord_394942).sum := by decide
  have hdescent : baseEnd_394942 < baseStart_394942 := by decide
  rcases family_descends (prefixWord ++ tailWord_394942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394980 : List Nat := [2, 3, 1, 1, 1, 3, 4, 1, 4]
def baseStart_394980 : Nat := 118140960795 + 394980 * 2 ^ 59
def prefixEnd_394980 : Nat := 4983230072969 + 3 ^ 40 * 394980 * 2
def baseEnd_394980 : Nat := 180279634589306553452023

theorem tailTrace_394980 : CollatzResearch.WordTrace tailWord_394980 prefixEnd_394980 180279634589306553452023 := by
  unfold tailWord_394980
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203052054531196029283197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9604069406041594705710929 7203052054531196029283197)
  ·
    refine ⟨2701144520449198510981199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7203052054531196029283197 2701144520449198510981199)
    ·
      refine ⟨4051716780673797766471799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2701144520449198510981199 4051716780673797766471799)
      ·
        refine ⟨6077575171010696649707699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4051716780673797766471799 6077575171010696649707699)
        ·
          refine ⟨9116362756516044974561549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6077575171010696649707699 9116362756516044974561549)
          ·
            refine ⟨3418636033693516865460581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9116362756516044974561549 3418636033693516865460581)
            ·
              refine ⟨640994256317534412273859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3418636033693516865460581 640994256317534412273859)
              ·
                refine ⟨961491384476301618410789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 640994256317534412273859 961491384476301618410789)
                ·
                  refine ⟨180279634589306553452023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961491384476301618410789 180279634589306553452023)
                  ·
                    rfl

theorem cell20_394980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 3, 4, 1, 4].length) (baseStart_394980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394980 prefixEnd_394980 := by exact prefixLift 394980
  have htrace : WordTrace (prefixWord ++ tailWord_394980) baseStart_394980 baseEnd_394980 := by
    simpa [prefixWord, tailWord_394980, baseEnd_394980] using wordTrace_append hprefix tailTrace_394980
  have hstable : (prefixWord ++ tailWord_394980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394980).length < 2 ^ (prefixWord ++ tailWord_394980).sum := by decide
  have hdescent : baseEnd_394980 < baseStart_394980 := by decide
  rcases family_descends (prefixWord ++ tailWord_394980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_394990 : List Nat := [4, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_394990 : Nat := 118140960795 + 394990 * 2 ^ 59
def prefixEnd_394990 : Nat := 4983230072969 + 3 ^ 40 * 394990 * 2
def baseEnd_394990 : Nat := 180284198861790963118649

theorem tailTrace_394990 : CollatzResearch.WordTrace tailWord_394990 prefixEnd_394990 180284198861790963118649 := by
  unfold tailWord_394990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1800808604878270470803803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9604312559350775844286949 1800808604878270470803803)
  ·
    refine ⟨2701212907317405706205705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1800808604878270470803803 2701212907317405706205705)
    ·
      refine ⟨2025909680488054279654279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701212907317405706205705 2025909680488054279654279)
      ·
        refine ⟨3038864520732081419481419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2025909680488054279654279 3038864520732081419481419)
        ·
          refine ⟨4558296781098122129222129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3038864520732081419481419 4558296781098122129222129)
          ·
            refine ⟨3418722585823591596916597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4558296781098122129222129 3418722585823591596916597)
            ·
              refine ⟨320505242420961712210931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3418722585823591596916597 320505242420961712210931)
              ·
                refine ⟨480757863631442568316397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 320505242420961712210931 480757863631442568316397)
                ·
                  refine ⟨180284198861790963118649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 480757863631442568316397 180284198861790963118649)
                  ·
                    rfl

theorem cell20_394990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_394990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_394990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_394990 prefixEnd_394990 := by exact prefixLift 394990
  have htrace : WordTrace (prefixWord ++ tailWord_394990) baseStart_394990 baseEnd_394990 := by
    simpa [prefixWord, tailWord_394990, baseEnd_394990] using wordTrace_append hprefix tailTrace_394990
  have hstable : (prefixWord ++ tailWord_394990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_394990).length < 2 ^ (prefixWord ++ tailWord_394990).sum := by decide
  have hdescent : baseEnd_394990 < baseStart_394990 := by decide
  rcases family_descends (prefixWord ++ tailWord_394990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395008 : List Nat := [2, 1, 1, 2, 1, 1, 2, 10]
def baseStart_395008 : Nat := 118140960795 + 395008 * 2 ^ 59
def prefixEnd_395008 : Nat := 4983230072969 + 3 ^ 40 * 395008 * 2
def baseEnd_395008 : Nat := 60097471517420966839525

theorem tailTrace_395008 : CollatzResearch.WordTrace tailWord_395008 prefixEnd_395008 60097471517420966839525 := by
  unfold tailWord_395008
  simp only [CollatzResearch.WordTrace]
  refine ⟨7203562676480476420292839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9604750235307301893723785 7203562676480476420292839)
  ·
    refine ⟨10805344014720714630439259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7203562676480476420292839 10805344014720714630439259)
    ·
      refine ⟨16208016022081071945658889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10805344014720714630439259 16208016022081071945658889)
      ·
        refine ⟨12156012016560803959244167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16208016022081071945658889 12156012016560803959244167)
        ·
          refine ⟨18234018024841205938866251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12156012016560803959244167 18234018024841205938866251)
          ·
            refine ⟨27351027037261808908299377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18234018024841205938866251 27351027037261808908299377)
            ·
              refine ⟨20513270277946356681224533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 27351027037261808908299377 20513270277946356681224533)
              ·
                refine ⟨60097471517420966839525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 20513270277946356681224533 60097471517420966839525)
                ·
                  rfl

theorem cell20_395008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_395008 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395008 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395008 prefixEnd_395008 := by exact prefixLift 395008
  have htrace : WordTrace (prefixWord ++ tailWord_395008) baseStart_395008 baseEnd_395008 := by
    simpa [prefixWord, tailWord_395008, baseEnd_395008] using wordTrace_append hprefix tailTrace_395008
  have hstable : (prefixWord ++ tailWord_395008).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395008).length < 2 ^ (prefixWord ++ tailWord_395008).sum := by decide
  have hdescent : baseEnd_395008 < baseStart_395008 := by decide
  rcases family_descends (prefixWord ++ tailWord_395008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395032 : List Nat := [2, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_395032 : Nat := 118140960795 + 395032 * 2 ^ 59
def prefixEnd_395032 : Nat := 4983230072969 + 3 ^ 40 * 395032 * 2
def baseEnd_395032 : Nat := 180303368806225483718477

theorem tailTrace_395032 : CollatzResearch.WordTrace tailWord_395032 prefixEnd_395032 180303368806225483718477 := by
  unfold tailWord_395032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204000352437002469729675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9605333803249336626306233 7204000352437002469729675)
  ·
    refine ⟨10806000528655503704594513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7204000352437002469729675 10806000528655503704594513)
    ·
      refine ⟨8104500396491627778445885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10806000528655503704594513 8104500396491627778445885)
      ·
        refine ⟨3039187648684360416917207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8104500396491627778445885 3039187648684360416917207)
        ·
          refine ⟨4558781473026540625375811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039187648684360416917207 4558781473026540625375811)
          ·
            refine ⟨6838172209539810938063717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4558781473026540625375811 6838172209539810938063717)
            ·
              refine ⟨1282157289288714550886947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6838172209539810938063717 1282157289288714550886947)
              ·
                refine ⟨1923235933933071826330421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1282157289288714550886947 1923235933933071826330421)
                ·
                  refine ⟨180303368806225483718477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1923235933933071826330421 180303368806225483718477)
                  ·
                    rfl

theorem cell20_395032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_395032 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395032 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395032 prefixEnd_395032 := by exact prefixLift 395032
  have htrace : WordTrace (prefixWord ++ tailWord_395032) baseStart_395032 baseEnd_395032 := by
    simpa [prefixWord, tailWord_395032, baseEnd_395032] using wordTrace_append hprefix tailTrace_395032
  have hstable : (prefixWord ++ tailWord_395032).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395032).length < 2 ^ (prefixWord ++ tailWord_395032).sum := by decide
  have hdescent : baseEnd_395032 < baseStart_395032 := by decide
  rcases family_descends (prefixWord ++ tailWord_395032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395038 : List Nat := [4, 3, 2, 2, 1, 1, 2, 5]
def baseStart_395038 : Nat := 118140960795 + 395038 * 2 ^ 59
def prefixEnd_395038 : Nat := 4983230072969 + 3 ^ 40 * 395038 * 2
def baseEnd_395038 : Nat := 60102035789905376506151

theorem tailTrace_395038 : CollatzResearch.WordTrace tailWord_395038 prefixEnd_395038 60102035789905376506151 := by
  unfold tailWord_395038
  simp only [CollatzResearch.WordTrace]
  refine ⟨1801027442856533495522221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9605479695234845309451845 1801027442856533495522221)
  ·
    refine ⟨675385291071200060820833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1801027442856533495522221 675385291071200060820833)
    ·
      refine ⟨506538968303400045615625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 675385291071200060820833 506538968303400045615625)
      ·
        refine ⟨379904226227550034211719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 506538968303400045615625 379904226227550034211719)
        ·
          refine ⟨569856339341325051317579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 379904226227550034211719 569856339341325051317579)
          ·
            refine ⟨854784509011987576976369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 569856339341325051317579 854784509011987576976369)
            ·
              refine ⟨641088381758990682732277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 854784509011987576976369 641088381758990682732277)
              ·
                refine ⟨60102035789905376506151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 641088381758990682732277 60102035789905376506151)
                ·
                  rfl

theorem cell20_395038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_395038 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395038 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395038 prefixEnd_395038 := by exact prefixLift 395038
  have htrace : WordTrace (prefixWord ++ tailWord_395038) baseStart_395038 baseEnd_395038 := by
    simpa [prefixWord, tailWord_395038, baseEnd_395038] using wordTrace_append hprefix tailTrace_395038
  have hstable : (prefixWord ++ tailWord_395038).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395038).length < 2 ^ (prefixWord ++ tailWord_395038).sum := by decide
  have hdescent : baseEnd_395038 < baseStart_395038 := by decide
  rcases family_descends (prefixWord ++ tailWord_395038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395084 : List Nat := [2, 2, 1, 3, 12]
def baseStart_395084 : Nat := 118140960795 + 395084 * 2 ^ 59
def prefixEnd_395084 : Nat := 4983230072969 + 3 ^ 40 * 395084 * 2
def baseEnd_395084 : Nat := 2226260531149931036851

theorem tailTrace_395084 : CollatzResearch.WordTrace tailWord_395084 prefixEnd_395084 2226260531149931036851 := by
  unfold tailWord_395084
  simp only [CollatzResearch.WordTrace]
  refine ⟨7204948650342808910176153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9606598200457078546901537 7204948650342808910176153)
  ·
    refine ⟨5403711487757106682632115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7204948650342808910176153 5403711487757106682632115)
    ·
      refine ⟨8105567231635660023948173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5403711487757106682632115 8105567231635660023948173)
      ·
        refine ⟨3039587711863372508980565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8105567231635660023948173 3039587711863372508980565)
        ·
          refine ⟨2226260531149931036851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 3039587711863372508980565 2226260531149931036851)
          ·
            rfl

theorem cell20_395084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 12].length) (baseStart_395084 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395084 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395084 prefixEnd_395084 := by exact prefixLift 395084
  have htrace : WordTrace (prefixWord ++ tailWord_395084) baseStart_395084 baseEnd_395084 := by
    simpa [prefixWord, tailWord_395084, baseEnd_395084] using wordTrace_append hprefix tailTrace_395084
  have hstable : (prefixWord ++ tailWord_395084).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395084).length < 2 ^ (prefixWord ++ tailWord_395084).sum := by decide
  have hdescent : baseEnd_395084 < baseStart_395084 := by decide
  rcases family_descends (prefixWord ++ tailWord_395084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395090 : List Nat := [3, 2, 2, 1, 1, 3, 4, 2, 2]
def baseStart_395090 : Nat := 118140960795 + 395090 * 2 ^ 59
def prefixEnd_395090 : Nat := 4983230072969 + 3 ^ 40 * 395090 * 2
def baseEnd_395090 : Nat := 180329841586635059784907

theorem tailTrace_395090 : CollatzResearch.WordTrace tailWord_395090 prefixEnd_395090 180329841586635059784907 := by
  unfold tailWord_395090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3602529034665970211267681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9606744092442587230047149 3602529034665970211267681)
  ·
    refine ⟨2701896775999477658450761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3602529034665970211267681 2701896775999477658450761)
    ·
      refine ⟨2026422581999608243838071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2701896775999477658450761 2026422581999608243838071)
      ·
        refine ⟨3039633872999412365757107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2026422581999608243838071 3039633872999412365757107)
        ·
          refine ⟨4559450809499118548635661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3039633872999412365757107 4559450809499118548635661)
          ·
            refine ⟨1709794053562169455738373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4559450809499118548635661 1709794053562169455738373)
            ·
              refine ⟨320586385042906772950945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1709794053562169455738373 320586385042906772950945)
              ·
                refine ⟨240439788782180079713209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320586385042906772950945 240439788782180079713209)
                ·
                  refine ⟨180329841586635059784907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240439788782180079713209 180329841586635059784907)
                  ·
                    rfl

theorem cell20_395090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 4, 2, 2].length) (baseStart_395090 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395090 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395090 prefixEnd_395090 := by exact prefixLift 395090
  have htrace : WordTrace (prefixWord ++ tailWord_395090) baseStart_395090 baseEnd_395090 := by
    simpa [prefixWord, tailWord_395090, baseEnd_395090] using wordTrace_append hprefix tailTrace_395090
  have hstable : (prefixWord ++ tailWord_395090).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395090).length < 2 ^ (prefixWord ++ tailWord_395090).sum := by decide
  have hdescent : baseEnd_395090 < baseStart_395090 := by decide
  rcases family_descends (prefixWord ++ tailWord_395090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395153 : List Nat := [1, 2, 2, 1, 1, 1, 5, 3, 4]
def baseStart_395153 : Nat := 118140960795 + 395153 * 2 ^ 59
def prefixEnd_395153 : Nat := 4983230072969 + 3 ^ 40 * 395153 * 2
def baseEnd_395153 : Nat := 180358596503286840684649

theorem tailTrace_395153 : CollatzResearch.WordTrace tailWord_395153 prefixEnd_395153 180358596503286840684649 := by
  unfold tailWord_395153
  simp only [CollatzResearch.WordTrace]
  refine ⟨14412413937435642604614113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9608275958290428403076075 14412413937435642604614113)
  ·
    refine ⟨10809310453076731953460585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14412413937435642604614113 10809310453076731953460585)
    ·
      refine ⟨8106982839807548965095439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10809310453076731953460585 8106982839807548965095439)
      ·
        refine ⟨12160474259711323447643159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8106982839807548965095439 12160474259711323447643159)
        ·
          refine ⟨18240711389566985171464739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12160474259711323447643159 18240711389566985171464739)
          ·
            refine ⟨27361067084350477757197109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18240711389566985171464739 27361067084350477757197109)
            ·
              refine ⟨2565100039157857289737229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 27361067084350477757197109 2565100039157857289737229)
              ·
                refine ⟨961912514684196483651461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2565100039157857289737229 961912514684196483651461)
                ·
                  refine ⟨180358596503286840684649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 961912514684196483651461 180358596503286840684649)
                  ·
                    rfl

theorem cell20_395153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 5, 3, 4].length) (baseStart_395153 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395153 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395153 prefixEnd_395153 := by exact prefixLift 395153
  have htrace : WordTrace (prefixWord ++ tailWord_395153) baseStart_395153 baseEnd_395153 := by
    simpa [prefixWord, tailWord_395153, baseEnd_395153] using wordTrace_append hprefix tailTrace_395153
  have hstable : (prefixWord ++ tailWord_395153).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395153).length < 2 ^ (prefixWord ++ tailWord_395153).sum := by decide
  have hdescent : baseEnd_395153 < baseStart_395153 := by decide
  rcases family_descends (prefixWord ++ tailWord_395153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395208 : List Nat := [2, 1, 3, 1, 4, 1, 3, 1, 4]
def baseStart_395208 : Nat := 118140960795 + 395208 * 2 ^ 59
def prefixEnd_395208 : Nat := 4983230072969 + 3 ^ 40 * 395208 * 2
def baseEnd_395208 : Nat := 180383700001951093851091

theorem tailTrace_395208 : CollatzResearch.WordTrace tailWord_395208 prefixEnd_395208 180383700001951093851091 := by
  unfold tailWord_395208
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207209976118193498933139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9609613301490924665244185 7207209976118193498933139)
  ·
    refine ⟨10810814964177290248399709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7207209976118193498933139 10810814964177290248399709)
    ·
      refine ⟨4054055611566483843149891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10810814964177290248399709 4054055611566483843149891)
      ·
        refine ⟨6081083417349725764724837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054055611566483843149891 6081083417349725764724837)
        ·
          refine ⟨1140203140753073580885907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6081083417349725764724837 1140203140753073580885907)
          ·
            refine ⟨1710304711129610371328861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1140203140753073580885907 1710304711129610371328861)
            ·
              refine ⟨641364266673603889248323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1710304711129610371328861 641364266673603889248323)
              ·
                refine ⟨962046400010405833872485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641364266673603889248323 962046400010405833872485)
                ·
                  refine ⟨180383700001951093851091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962046400010405833872485 180383700001951093851091)
                  ·
                    rfl

theorem cell20_395208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4].length) (baseStart_395208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395208 prefixEnd_395208 := by exact prefixLift 395208
  have htrace : WordTrace (prefixWord ++ tailWord_395208) baseStart_395208 baseEnd_395208 := by
    simpa [prefixWord, tailWord_395208, baseEnd_395208] using wordTrace_append hprefix tailTrace_395208
  have hstable : (prefixWord ++ tailWord_395208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395208).length < 2 ^ (prefixWord ++ tailWord_395208).sum := by decide
  have hdescent : baseEnd_395208 < baseStart_395208 := by decide
  rcases family_descends (prefixWord ++ tailWord_395208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395218 : List Nat := [3, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_395218 : Nat := 118140960795 + 395218 * 2 ^ 59
def prefixEnd_395218 : Nat := 4983230072969 + 3 ^ 40 * 395218 * 2
def baseEnd_395218 : Nat := 180388264274435503517717

theorem tailTrace_395218 : CollatzResearch.WordTrace tailWord_395218 prefixEnd_395218 180388264274435503517717 := by
  unfold tailWord_395218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3603696170550039676432577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9609856454800105803820205 3603696170550039676432577)
  ·
    refine ⟨2702772127912529757324433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3603696170550039676432577 2702772127912529757324433)
    ·
      refine ⟨2027079095934397317993325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2702772127912529757324433 2027079095934397317993325)
      ·
        refine ⟨760154660975398994247497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2027079095934397317993325 760154660975398994247497)
        ·
          refine ⟨570115995731549245685623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760154660975398994247497 570115995731549245685623)
          ·
            refine ⟨855173993597323868528435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570115995731549245685623 855173993597323868528435)
            ·
              refine ⟨1282760990395985802792653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855173993597323868528435 1282760990395985802792653)
              ·
                refine ⟨481035371398494676047245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1282760990395985802792653 481035371398494676047245)
                ·
                  refine ⟨180388264274435503517717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481035371398494676047245 180388264274435503517717)
                  ·
                    rfl

theorem cell20_395218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_395218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395218 prefixEnd_395218 := by exact prefixLift 395218
  have htrace : WordTrace (prefixWord ++ tailWord_395218) baseStart_395218 baseEnd_395218 := by
    simpa [prefixWord, tailWord_395218, baseEnd_395218] using wordTrace_append hprefix tailTrace_395218
  have hstable : (prefixWord ++ tailWord_395218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395218).length < 2 ^ (prefixWord ++ tailWord_395218).sum := by decide
  have hdescent : baseEnd_395218 < baseStart_395218 := by decide
  rcases family_descends (prefixWord ++ tailWord_395218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395236 : List Nat := [2, 3, 1, 1, 1, 1, 3, 8]
def baseStart_395236 : Nat := 118140960795 + 395236 * 2 ^ 59
def prefixEnd_395236 : Nat := 4983230072969 + 3 ^ 40 * 395236 * 2
def baseEnd_395236 : Nat := 60132159988302480305881

theorem tailTrace_395236 : CollatzResearch.WordTrace tailWord_395236 prefixEnd_395236 60132159988302480305881 := by
  unfold tailWord_395236
  simp only [CollatzResearch.WordTrace]
  refine ⟨7207720598067473889942781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9610294130756631853257041 7207720598067473889942781)
  ·
    refine ⟨2702895224275302708728543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7207720598067473889942781 2702895224275302708728543)
    ·
      refine ⟨4054342836412954063092815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2702895224275302708728543 4054342836412954063092815)
      ·
        refine ⟨6081514254619431094639223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4054342836412954063092815 6081514254619431094639223)
        ·
          refine ⟨9122271381929146641958835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6081514254619431094639223 9122271381929146641958835)
          ·
            refine ⟨13683407072893719962938253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9122271381929146641958835 13683407072893719962938253)
            ·
              refine ⟨5131277652335144986101845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 13683407072893719962938253 5131277652335144986101845)
              ·
                refine ⟨60132159988302480305881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5131277652335144986101845 60132159988302480305881)
                ·
                  rfl

theorem cell20_395236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_395236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395236 prefixEnd_395236 := by exact prefixLift 395236
  have htrace : WordTrace (prefixWord ++ tailWord_395236) baseStart_395236 baseEnd_395236 := by
    simpa [prefixWord, tailWord_395236, baseEnd_395236] using wordTrace_append hprefix tailTrace_395236
  have hstable : (prefixWord ++ tailWord_395236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395236).length < 2 ^ (prefixWord ++ tailWord_395236).sum := by decide
  have hdescent : baseEnd_395236 < baseStart_395236 := by decide
  rcases family_descends (prefixWord ++ tailWord_395236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395243 : List Nat := [1, 1, 1, 1, 2, 3, 1, 3, 7]
def baseStart_395243 : Nat := 118140960795 + 395243 * 2 ^ 59
def prefixEnd_395243 : Nat := 4983230072969 + 3 ^ 40 * 395243 * 2
def baseEnd_395243 : Nat := 180399674955646527684281

theorem tailTrace_395243 : CollatzResearch.WordTrace tailWord_395243 prefixEnd_395243 180399674955646527684281 := by
  unfold tailWord_395243
  simp only [CollatzResearch.WordTrace]
  refine ⟨14415696507109587975390383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9610464338073058650260255 14415696507109587975390383)
  ·
    refine ⟨21623544760664381963085575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14415696507109587975390383 21623544760664381963085575)
    ·
      refine ⟨32435317140996572944628363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21623544760664381963085575 32435317140996572944628363)
      ·
        refine ⟨48652975711494859416942545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32435317140996572944628363 48652975711494859416942545)
        ·
          refine ⟨36489731783621144562706909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 48652975711494859416942545 36489731783621144562706909)
          ·
            refine ⟨13683649418857929211015091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36489731783621144562706909 13683649418857929211015091)
            ·
              refine ⟨20525474128286893816522637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13683649418857929211015091 20525474128286893816522637)
              ·
                refine ⟨7697052798107585181195989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 20525474128286893816522637 7697052798107585181195989)
                ·
                  refine ⟨180399674955646527684281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 7697052798107585181195989 180399674955646527684281)
                  ·
                    rfl

theorem cell20_395243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 3, 7].length) (baseStart_395243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395243 prefixEnd_395243 := by exact prefixLift 395243
  have htrace : WordTrace (prefixWord ++ tailWord_395243) baseStart_395243 baseEnd_395243 := by
    simpa [prefixWord, tailWord_395243, baseEnd_395243] using wordTrace_append hprefix tailTrace_395243
  have hstable : (prefixWord ++ tailWord_395243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395243).length < 2 ^ (prefixWord ++ tailWord_395243).sum := by decide
  have hdescent : baseEnd_395243 < baseStart_395243 := by decide
  rcases family_descends (prefixWord ++ tailWord_395243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395281 : List Nat := [1, 2, 2, 1, 1, 2, 1, 1, 9]
def baseStart_395281 : Nat := 118140960795 + 395281 * 2 ^ 59
def prefixEnd_395281 : Nat := 4983230072969 + 3 ^ 40 * 395281 * 2
def baseEnd_395281 : Nat := 180417019191087284417459

theorem tailTrace_395281 : CollatzResearch.WordTrace tailWord_395281 prefixEnd_395281 180417019191087284417459 := by
  unfold tailWord_395281
  simp only [CollatzResearch.WordTrace]
  refine ⟨14417082480971920465273697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9611388320647946976849131 14417082480971920465273697)
  ·
    refine ⟨10812811860728940348955273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14417082480971920465273697 10812811860728940348955273)
    ·
      refine ⟨8109608895546705261716455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10812811860728940348955273 8109608895546705261716455)
      ·
        refine ⟨12164413343320057892574683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8109608895546705261716455 12164413343320057892574683)
        ·
          refine ⟨18246620014980086838862025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12164413343320057892574683 18246620014980086838862025)
          ·
            refine ⟨13684965011235065129146519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 18246620014980086838862025 13684965011235065129146519)
            ·
              refine ⟨20527447516852597693719779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13684965011235065129146519 20527447516852597693719779)
              ·
                refine ⟨30791171275278896540579669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 20527447516852597693719779 30791171275278896540579669)
                ·
                  refine ⟨180417019191087284417459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 30791171275278896540579669 180417019191087284417459)
                  ·
                    rfl

theorem cell20_395281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 1, 1, 9].length) (baseStart_395281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395281 prefixEnd_395281 := by exact prefixLift 395281
  have htrace : WordTrace (prefixWord ++ tailWord_395281) baseStart_395281 baseEnd_395281 := by
    simpa [prefixWord, tailWord_395281, baseEnd_395281] using wordTrace_append hprefix tailTrace_395281
  have hstable : (prefixWord ++ tailWord_395281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395281).length < 2 ^ (prefixWord ++ tailWord_395281).sum := by decide
  have hdescent : baseEnd_395281 < baseStart_395281 := by decide
  rcases family_descends (prefixWord ++ tailWord_395281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395298 : List Nat := [3, 3, 1, 1, 1, 2, 2, 2, 5]
def baseStart_395298 : Nat := 118140960795 + 395298 * 2 ^ 59
def prefixEnd_395298 : Nat := 4983230072969 + 3 ^ 40 * 395298 * 2
def baseEnd_395298 : Nat := 180424778454310780850723

theorem tailTrace_395298 : CollatzResearch.WordTrace tailWord_395298 prefixEnd_395298 180424778454310780850723 := by
  unfold tailWord_395298
  simp only [CollatzResearch.WordTrace]
  refine ⟨3604425630477583092160637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9611801681273554912428365 3604425630477583092160637)
  ·
    refine ⟨1351659611429093659560239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3604425630477583092160637 1351659611429093659560239)
    ·
      refine ⟨2027489417143640489340359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1351659611429093659560239 2027489417143640489340359)
      ·
        refine ⟨3041234125715460734010539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2027489417143640489340359 3041234125715460734010539)
        ·
          refine ⟨4561851188573191101015809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3041234125715460734010539 4561851188573191101015809)
          ·
            refine ⟨3421388391429893325761857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4561851188573191101015809 3421388391429893325761857)
            ·
              refine ⟨2566041293572419994321393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3421388391429893325761857 2566041293572419994321393)
              ·
                refine ⟨1924530970179314995741045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2566041293572419994321393 1924530970179314995741045)
                ·
                  refine ⟨180424778454310780850723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1924530970179314995741045 180424778454310780850723)
                  ·
                    rfl

theorem cell20_395298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_395298 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395298 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395298 prefixEnd_395298 := by exact prefixLift 395298
  have htrace : WordTrace (prefixWord ++ tailWord_395298) baseStart_395298 baseEnd_395298 := by
    simpa [prefixWord, tailWord_395298, baseEnd_395298] using wordTrace_append hprefix tailTrace_395298
  have hstable : (prefixWord ++ tailWord_395298).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395298).length < 2 ^ (prefixWord ++ tailWord_395298).sum := by decide
  have hdescent : baseEnd_395298 < baseStart_395298 := by decide
  rcases family_descends (prefixWord ++ tailWord_395298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395301 : List Nat := [1, 3, 1, 2, 2, 4, 2, 3, 2]
def baseStart_395301 : Nat := 118140960795 + 395301 * 2 ^ 59
def prefixEnd_395301 : Nat := 4983230072969 + 3 ^ 40 * 395301 * 2
def baseEnd_395301 : Nat := 180426147736056103750711

theorem tailTrace_395301 : CollatzResearch.WordTrace tailWord_395301 prefixEnd_395301 180426147736056103750711 := by
  unfold tailWord_395301
  simp only [CollatzResearch.WordTrace]
  refine ⟨14417811940899463881001757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9611874627266309254001171 14417811940899463881001757)
  ·
    refine ⟨5406679477837298955375659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14417811940899463881001757 5406679477837298955375659)
    ·
      refine ⟨8110019216755948433063489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5406679477837298955375659 8110019216755948433063489)
      ·
        refine ⟨6082514412566961324797617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8110019216755948433063489 6082514412566961324797617)
        ·
          refine ⟨4561885809425220993598213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6082514412566961324797617 4561885809425220993598213)
          ·
            refine ⟨855353589267228936299665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4561885809425220993598213 855353589267228936299665)
            ·
              refine ⟨641515191950421702224749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855353589267228936299665 641515191950421702224749)
              ·
                refine ⟨240568196981408138334281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641515191950421702224749 240568196981408138334281)
                ·
                  refine ⟨180426147736056103750711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240568196981408138334281 180426147736056103750711)
                  ·
                    rfl

theorem cell20_395301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 4, 2, 3, 2].length) (baseStart_395301 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395301 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395301 prefixEnd_395301 := by exact prefixLift 395301
  have htrace : WordTrace (prefixWord ++ tailWord_395301) baseStart_395301 baseEnd_395301 := by
    simpa [prefixWord, tailWord_395301, baseEnd_395301] using wordTrace_append hprefix tailTrace_395301
  have hstable : (prefixWord ++ tailWord_395301).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395301).length < 2 ^ (prefixWord ++ tailWord_395301).sum := by decide
  have hdescent : baseEnd_395301 < baseStart_395301 := by decide
  rcases family_descends (prefixWord ++ tailWord_395301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395312 : List Nat := [2, 1, 1, 1, 2, 6, 7]
def baseStart_395312 : Nat := 118140960795 + 395312 * 2 ^ 59
def prefixEnd_395312 : Nat := 4983230072969 + 3 ^ 40 * 395312 * 2
def baseEnd_395312 : Nat := 20047907603976550487111

theorem tailTrace_395312 : CollatzResearch.WordTrace tailWord_395312 prefixEnd_395312 20047907603976550487111 := by
  unfold tailWord_395312
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209106571929806379826095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9612142095906408506434793 7209106571929806379826095)
  ·
    refine ⟨10813659857894709569739143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7209106571929806379826095 10813659857894709569739143)
    ·
      refine ⟨16220489786842064354608715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10813659857894709569739143 16220489786842064354608715)
      ·
        refine ⟨24330734680263096531913073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16220489786842064354608715 24330734680263096531913073)
        ·
          refine ⟨18248051010197322398934805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 24330734680263096531913073 18248051010197322398934805)
          ·
            refine ⟨855377391102999487450069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 18248051010197322398934805 855377391102999487450069)
            ·
              refine ⟨20047907603976550487111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 855377391102999487450069 20047907603976550487111)
              ·
                rfl

theorem cell20_395312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_395312 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395312 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395312 prefixEnd_395312 := by exact prefixLift 395312
  have htrace : WordTrace (prefixWord ++ tailWord_395312) baseStart_395312 baseEnd_395312 := by
    simpa [prefixWord, tailWord_395312, baseEnd_395312] using wordTrace_append hprefix tailTrace_395312
  have hstable : (prefixWord ++ tailWord_395312).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395312).length < 2 ^ (prefixWord ++ tailWord_395312).sum := by decide
  have hdescent : baseEnd_395312 < baseStart_395312 := by decide
  rcases family_descends (prefixWord ++ tailWord_395312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395356 : List Nat := [2, 2, 4, 1, 1, 4, 1, 3, 2]
def baseStart_395356 : Nat := 118140960795 + 395356 * 2 ^ 59
def prefixEnd_395356 : Nat := 4983230072969 + 3 ^ 40 * 395356 * 2
def baseEnd_395356 : Nat := 180451251234720356917153

theorem tailTrace_395356 : CollatzResearch.WordTrace tailWord_395356 prefixEnd_395356 180451251234720356917153 := by
  unfold tailWord_395356
  simp only [CollatzResearch.WordTrace]
  refine ⟨7209908977850104137126961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9613211970466805516169281 7209908977850104137126961)
  ·
    refine ⟨5407431733387578102845221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7209908977850104137126961 5407431733387578102845221)
    ·
      refine ⟨1013893450010170894283479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5407431733387578102845221 1013893450010170894283479)
      ·
        refine ⟨1520840175015256341425219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1013893450010170894283479 1520840175015256341425219)
        ·
          refine ⟨2281260262522884512137829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520840175015256341425219 2281260262522884512137829)
          ·
            refine ⟨427736299223040846025843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2281260262522884512137829 427736299223040846025843)
            ·
              refine ⟨641604448834561269038765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427736299223040846025843 641604448834561269038765)
              ·
                refine ⟨240601668312960475889537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641604448834561269038765 240601668312960475889537)
                ·
                  refine ⟨180451251234720356917153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240601668312960475889537 180451251234720356917153)
                  ·
                    rfl

theorem cell20_395356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 4, 1, 3, 2].length) (baseStart_395356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395356 prefixEnd_395356 := by exact prefixLift 395356
  have htrace : WordTrace (prefixWord ++ tailWord_395356) baseStart_395356 baseEnd_395356 := by
    simpa [prefixWord, tailWord_395356, baseEnd_395356] using wordTrace_append hprefix tailTrace_395356
  have hstable : (prefixWord ++ tailWord_395356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395356).length < 2 ^ (prefixWord ++ tailWord_395356).sum := by decide
  have hdescent : baseEnd_395356 < baseStart_395356 := by decide
  rcases family_descends (prefixWord ++ tailWord_395356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395374 : List Nat := [4, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_395374 : Nat := 118140960795 + 395374 * 2 ^ 59
def prefixEnd_395374 : Nat := 4983230072969 + 3 ^ 40 * 395374 * 2
def baseEnd_395374 : Nat := 180459466925192294317079

theorem tailTrace_395374 : CollatzResearch.WordTrace tailWord_395374 prefixEnd_395374 180459466925192294317079 := by
  unfold tailWord_395374
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802559308704374668551147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9613649646423331565606117 1802559308704374668551147)
  ·
    refine ⟨2703838963056562002826721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1802559308704374668551147 2703838963056562002826721)
    ·
      refine ⟨2027879222292421502120041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2703838963056562002826721 2027879222292421502120041)
      ·
        refine ⟨1520909416719316126590031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2027879222292421502120041 1520909416719316126590031)
        ·
          refine ⟨2281364125078974189885047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1520909416719316126590031 2281364125078974189885047)
          ·
            refine ⟨3422046187618461284827571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2281364125078974189885047 3422046187618461284827571)
            ·
              refine ⟨5133069281427691927241357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3422046187618461284827571 5133069281427691927241357)
              ·
                refine ⟨1924900980535384472715509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5133069281427691927241357 1924900980535384472715509)
                ·
                  refine ⟨180459466925192294317079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1924900980535384472715509 180459466925192294317079)
                  ·
                    rfl

theorem cell20_395374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_395374 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395374 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395374 prefixEnd_395374 := by exact prefixLift 395374
  have htrace : WordTrace (prefixWord ++ tailWord_395374) baseStart_395374 baseEnd_395374 := by
    simpa [prefixWord, tailWord_395374, baseEnd_395374] using wordTrace_append hprefix tailTrace_395374
  have hstable : (prefixWord ++ tailWord_395374).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395374).length < 2 ^ (prefixWord ++ tailWord_395374).sum := by decide
  have hdescent : baseEnd_395374 < baseStart_395374 := by decide
  rcases family_descends (prefixWord ++ tailWord_395374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395377 : List Nat := [1, 2, 2, 2, 1, 1, 7, 2, 2]
def baseStart_395377 : Nat := 118140960795 + 395377 * 2 ^ 59
def prefixEnd_395377 : Nat := 4983230072969 + 3 ^ 40 * 395377 * 2
def baseEnd_395377 : Nat := 180460836206937617217067

theorem tailTrace_395377 : CollatzResearch.WordTrace tailWord_395377 prefixEnd_395377 180460836206937617217067 := by
  unfold tailWord_395377
  simp only [CollatzResearch.WordTrace]
  refine ⟨14420583888624128860768385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9613722592416085907178923 14420583888624128860768385)
  ·
    refine ⟨10815437916468096645576289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14420583888624128860768385 10815437916468096645576289)
    ·
      refine ⟨8111578437351072484182217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10815437916468096645576289 8111578437351072484182217)
      ·
        refine ⟨6083683828013304363136663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8111578437351072484182217 6083683828013304363136663)
        ·
          refine ⟨9125525742019956544704995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083683828013304363136663 9125525742019956544704995)
          ·
            refine ⟨13688288613029934817057493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9125525742019956544704995 13688288613029934817057493)
            ·
              refine ⟨320819264367889097274785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 13688288613029934817057493 320819264367889097274785)
              ·
                refine ⟨240614448275916822956089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320819264367889097274785 240614448275916822956089)
                ·
                  refine ⟨180460836206937617217067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240614448275916822956089 180460836206937617217067)
                  ·
                    rfl

theorem cell20_395377_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 7, 2, 2].length) (baseStart_395377 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395377 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395377 prefixEnd_395377 := by exact prefixLift 395377
  have htrace : WordTrace (prefixWord ++ tailWord_395377) baseStart_395377 baseEnd_395377 := by
    simpa [prefixWord, tailWord_395377, baseEnd_395377] using wordTrace_append hprefix tailTrace_395377
  have hstable : (prefixWord ++ tailWord_395377).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395377).length < 2 ^ (prefixWord ++ tailWord_395377).sum := by decide
  have hdescent : baseEnd_395377 < baseStart_395377 := by decide
  rcases family_descends (prefixWord ++ tailWord_395377) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395388 : List Nat := [2, 2, 2, 1, 1, 4, 1, 7]
def baseStart_395388 : Nat := 118140960795 + 395388 * 2 ^ 59
def prefixEnd_395388 : Nat := 4983230072969 + 3 ^ 40 * 395388 * 2
def baseEnd_395388 : Nat := 60155285635556822616785

theorem tailTrace_395388 : CollatzResearch.WordTrace tailWord_395388 prefixEnd_395388 60155285635556822616785 := by
  unfold tailWord_395388
  simp only [CollatzResearch.WordTrace]
  refine ⟨7210492545792138869709409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9613990061056185159612545 7210492545792138869709409)
  ·
    refine ⟨5407869409344104152282057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7210492545792138869709409 5407869409344104152282057)
    ·
      refine ⟨4055902057008078114211543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5407869409344104152282057 4055902057008078114211543)
      ·
        refine ⟨6083853085512117171317315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4055902057008078114211543 6083853085512117171317315)
        ·
          refine ⟨9125779628268175756975973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6083853085512117171317315 9125779628268175756975973)
          ·
            refine ⟨1711083680300282954432995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9125779628268175756975973 1711083680300282954432995)
            ·
              refine ⟨2566625520450424431649493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1711083680300282954432995 2566625520450424431649493)
              ·
                refine ⟨60155285635556822616785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2566625520450424431649493 60155285635556822616785)
                ·
                  rfl

theorem cell20_395388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 7].length) (baseStart_395388 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395388 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395388 prefixEnd_395388 := by exact prefixLift 395388
  have htrace : WordTrace (prefixWord ++ tailWord_395388) baseStart_395388 baseEnd_395388 := by
    simpa [prefixWord, tailWord_395388, baseEnd_395388] using wordTrace_append hprefix tailTrace_395388
  have hstable : (prefixWord ++ tailWord_395388).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395388).length < 2 ^ (prefixWord ++ tailWord_395388).sum := by decide
  have hdescent : baseEnd_395388 < baseStart_395388 := by decide
  rcases family_descends (prefixWord ++ tailWord_395388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395422 : List Nat := [4, 3, 1, 1, 4, 7]
def baseStart_395422 : Nat := 118140960795 + 395422 * 2 ^ 59
def prefixEnd_395422 : Nat := 4983230072969 + 3 ^ 40 * 395422 * 2
def baseEnd_395422 : Nat := 6684495386411757804329

theorem tailTrace_395422 : CollatzResearch.WordTrace tailWord_395422 prefixEnd_395422 6684495386411757804329 := by
  unfold tailWord_395422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1802778146682637693269565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9614816782307401030771013 1802778146682637693269565)
  ·
    refine ⟨676041805005989134976087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1802778146682637693269565 676041805005989134976087)
    ·
      refine ⟨1014062707508983702464131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 676041805005989134976087 1014062707508983702464131)
      ·
        refine ⟨1521094061263475553696197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014062707508983702464131 1521094061263475553696197)
        ·
          refine ⟨285205136486901666318037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1521094061263475553696197 285205136486901666318037)
          ·
            refine ⟨6684495386411757804329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 285205136486901666318037 6684495386411757804329)
            ·
              rfl

theorem cell20_395422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 4, 7].length) (baseStart_395422 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395422 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395422 prefixEnd_395422 := by exact prefixLift 395422
  have htrace : WordTrace (prefixWord ++ tailWord_395422) baseStart_395422 baseEnd_395422 := by
    simpa [prefixWord, tailWord_395422, baseEnd_395422] using wordTrace_append hprefix tailTrace_395422
  have hstable : (prefixWord ++ tailWord_395422).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395422).length < 2 ^ (prefixWord ++ tailWord_395422).sum := by decide
  have hdescent : baseEnd_395422 < baseStart_395422 := by decide
  rcases family_descends (prefixWord ++ tailWord_395422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395450 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 3]
def baseStart_395450 : Nat := 118140960795 + 395450 * 2 ^ 59
def prefixEnd_395450 : Nat := 4983230072969 + 3 ^ 40 * 395450 * 2
def baseEnd_395450 : Nat := 180494155396073807783435

theorem tailTrace_395450 : CollatzResearch.WordTrace tailWord_395450 prefixEnd_395450 180494155396073807783435 := by
  unfold tailWord_395450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3605811604339915582043951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9615497611573108218783869 3605811604339915582043951)
  ·
    refine ⟨5408717406509873373065927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3605811604339915582043951 5408717406509873373065927)
    ·
      refine ⟨8113076109764810059598891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5408717406509873373065927 8113076109764810059598891)
      ·
        refine ⟨12169614164647215089398337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8113076109764810059598891 12169614164647215089398337)
        ·
          refine ⟨9127210623485411317048753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12169614164647215089398337 9127210623485411317048753)
          ·
            refine ⟨6845407967614058487786565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9127210623485411317048753 6845407967614058487786565)
            ·
              refine ⟨1283513993927635966459981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6845407967614058487786565 1283513993927635966459981)
              ·
                refine ⟨481317747722863487422493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1283513993927635966459981 481317747722863487422493)
                ·
                  refine ⟨180494155396073807783435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481317747722863487422493 180494155396073807783435)
                  ·
                    rfl

theorem cell20_395450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_395450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395450 prefixEnd_395450 := by exact prefixLift 395450
  have htrace : WordTrace (prefixWord ++ tailWord_395450) baseStart_395450 baseEnd_395450 := by
    simpa [prefixWord, tailWord_395450, baseEnd_395450] using wordTrace_append hprefix tailTrace_395450
  have hstable : (prefixWord ++ tailWord_395450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395450).length < 2 ^ (prefixWord ++ tailWord_395450).sum := by decide
  have hdescent : baseEnd_395450 < baseStart_395450 := by decide
  rcases family_descends (prefixWord ++ tailWord_395450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395460 : List Nat := [2, 3, 3, 1, 2, 2, 3, 4]
def baseStart_395460 : Nat := 118140960795 + 395460 * 2 ^ 59
def prefixEnd_395460 : Nat := 4983230072969 + 3 ^ 40 * 395460 * 2
def baseEnd_395460 : Nat := 60166239889519405816687

theorem tailTrace_395460 : CollatzResearch.WordTrace tailWord_395460 prefixEnd_395460 60166239889519405816687 := by
  unfold tailWord_395460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7211805573661717018019917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9615740764882289357359889 7211805573661717018019917)
  ·
    refine ⟨2704427090123143881757469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7211805573661717018019917 2704427090123143881757469)
    ·
      refine ⟨1014160158796178955659051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2704427090123143881757469 1014160158796178955659051)
      ·
        refine ⟨1521240238194268433488577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1014160158796178955659051 1521240238194268433488577)
        ·
          refine ⟨1140930178645701325116433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1521240238194268433488577 1140930178645701325116433)
          ·
            refine ⟨855697633984275993837325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1140930178645701325116433 855697633984275993837325)
            ·
              refine ⟨320886612744103497688997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855697633984275993837325 320886612744103497688997)
              ·
                refine ⟨60166239889519405816687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 320886612744103497688997 60166239889519405816687)
                ·
                  rfl

theorem cell20_395460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 3, 4].length) (baseStart_395460 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395460 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395460 prefixEnd_395460 := by exact prefixLift 395460
  have htrace : WordTrace (prefixWord ++ tailWord_395460) baseStart_395460 baseEnd_395460 := by
    simpa [prefixWord, tailWord_395460, baseEnd_395460] using wordTrace_append hprefix tailTrace_395460
  have hstable : (prefixWord ++ tailWord_395460).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395460).length < 2 ^ (prefixWord ++ tailWord_395460).sum := by decide
  have hdescent : baseEnd_395460 < baseStart_395460 := by decide
  rcases family_descends (prefixWord ++ tailWord_395460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395471 : List Nat := [1, 1, 2, 1, 1, 3, 4, 2, 5]
def baseStart_395471 : Nat := 118140960795 + 395471 * 2 ^ 59
def prefixEnd_395471 : Nat := 4983230072969 + 3 ^ 40 * 395471 * 2
def baseEnd_395471 : Nat := 180503740368291068083349

theorem tailTrace_395471 : CollatzResearch.WordTrace tailWord_395471 prefixEnd_395471 180503740368291068083349 := by
  unfold tailWord_395471
  simp only [CollatzResearch.WordTrace]
  refine ⟨14424012350283582914690267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9616008233522388609793511 14424012350283582914690267)
  ·
    refine ⟨21636018525425374372035401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14424012350283582914690267 21636018525425374372035401)
    ·
      refine ⟨16227013894069030779026551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 21636018525425374372035401 16227013894069030779026551)
      ·
        refine ⟨24340520841103546168539827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16227013894069030779026551 24340520841103546168539827)
        ·
          refine ⟨36510781261655319252809741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 24340520841103546168539827 36510781261655319252809741)
          ·
            refine ⟨13691542973120744719803653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 36510781261655319252809741 13691542973120744719803653)
            ·
              refine ⟨2567164307460139634963185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13691542973120744719803653 2567164307460139634963185)
              ·
                refine ⟨1925373230595104726222389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2567164307460139634963185 1925373230595104726222389)
                ·
                  refine ⟨180503740368291068083349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925373230595104726222389 180503740368291068083349)
                  ·
                    rfl

theorem cell20_395471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 4, 2, 5].length) (baseStart_395471 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395471 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395471 prefixEnd_395471 := by exact prefixLift 395471
  have htrace : WordTrace (prefixWord ++ tailWord_395471) baseStart_395471 baseEnd_395471 := by
    simpa [prefixWord, tailWord_395471, baseEnd_395471] using wordTrace_append hprefix tailTrace_395471
  have hstable : (prefixWord ++ tailWord_395471).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395471).length < 2 ^ (prefixWord ++ tailWord_395471).sum := by decide
  have hdescent : baseEnd_395471 < baseStart_395471 := by decide
  rcases family_descends (prefixWord ++ tailWord_395471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395484 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 5]
def baseStart_395484 : Nat := 118140960795 + 395484 * 2 ^ 59
def prefixEnd_395484 : Nat := 4983230072969 + 3 ^ 40 * 395484 * 2
def baseEnd_395484 : Nat := 180509673922520800649963

theorem tailTrace_395484 : CollatzResearch.WordTrace tailWord_395484 prefixEnd_395484 180509673922520800649963 := by
  unfold tailWord_395484
  simp only [CollatzResearch.WordTrace]
  refine ⟨7212243249618243067456753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9616324332824324089942337 7212243249618243067456753)
  ·
    refine ⟨5409182437213682300592565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7212243249618243067456753 5409182437213682300592565)
    ·
      refine ⟨507110853488782715680553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5409182437213682300592565 507110853488782715680553)
      ·
        refine ⟨380333140116587036760415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 507110853488782715680553 380333140116587036760415)
        ·
          refine ⟨570499710174880555140623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380333140116587036760415 570499710174880555140623)
          ·
            refine ⟨855749565262320832710935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570499710174880555140623 855749565262320832710935)
            ·
              refine ⟨1283624347893481249066403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 855749565262320832710935 1283624347893481249066403)
              ·
                refine ⟨1925436521840221873599605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283624347893481249066403 1925436521840221873599605)
                ·
                  refine ⟨180509673922520800649963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925436521840221873599605 180509673922520800649963)
                  ·
                    rfl

theorem cell20_395484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5].length) (baseStart_395484 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395484 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395484 prefixEnd_395484 := by exact prefixLift 395484
  have htrace : WordTrace (prefixWord ++ tailWord_395484) baseStart_395484 baseEnd_395484 := by
    simpa [prefixWord, tailWord_395484, baseEnd_395484] using wordTrace_append hprefix tailTrace_395484
  have hstable : (prefixWord ++ tailWord_395484).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395484).length < 2 ^ (prefixWord ++ tailWord_395484).sum := by decide
  have hdescent : baseEnd_395484 < baseStart_395484 := by decide
  rcases family_descends (prefixWord ++ tailWord_395484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395491 : List Nat := [1, 1, 1, 8, 1, 1, 2, 1, 4]
def baseStart_395491 : Nat := 118140960795 + 395491 * 2 ^ 59
def prefixEnd_395491 : Nat := 4983230072969 + 3 ^ 40 * 395491 * 2
def baseEnd_395491 : Nat := 180512868913259887416601

theorem tailTrace_395491 : CollatzResearch.WordTrace tailWord_395491 prefixEnd_395491 180512868913259887416601 := by
  unfold tailWord_395491
  simp only [CollatzResearch.WordTrace]
  refine ⟨14424741810211126330418327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9616494540140750886945551 14424741810211126330418327)
  ·
    refine ⟨21637112715316689495627491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14424741810211126330418327 21637112715316689495627491)
    ·
      refine ⟨32455669072975034243441237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21637112715316689495627491 32455669072975034243441237)
      ·
        refine ⟨380339871948926182540327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 32455669072975034243441237 380339871948926182540327)
        ·
          refine ⟨570509807923389273810491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380339871948926182540327 570509807923389273810491)
          ·
            refine ⟨855764711885083910715737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570509807923389273810491 855764711885083910715737)
            ·
              refine ⟨641823533913812933036803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855764711885083910715737 641823533913812933036803)
              ·
                refine ⟨962735300870719399555205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 641823533913812933036803 962735300870719399555205)
                ·
                  refine ⟨180512868913259887416601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 962735300870719399555205 180512868913259887416601)
                  ·
                    rfl

theorem cell20_395491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 2, 1, 4].length) (baseStart_395491 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395491 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395491 prefixEnd_395491 := by exact prefixLift 395491
  have htrace : WordTrace (prefixWord ++ tailWord_395491) baseStart_395491 baseEnd_395491 := by
    simpa [prefixWord, tailWord_395491, baseEnd_395491] using wordTrace_append hprefix tailTrace_395491
  have hstable : (prefixWord ++ tailWord_395491).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395491).length < 2 ^ (prefixWord ++ tailWord_395491).sum := by decide
  have hdescent : baseEnd_395491 < baseStart_395491 := by decide
  rcases family_descends (prefixWord ++ tailWord_395491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395502 : List Nat := [4, 1, 2, 1, 1, 1, 1, 9]
def baseStart_395502 : Nat := 118140960795 + 395502 * 2 ^ 59
def prefixEnd_395502 : Nat := 4983230072969 + 3 ^ 40 * 395502 * 2
def baseEnd_395502 : Nat := 60172629870997579349963

theorem tailTrace_395502 : CollatzResearch.WordTrace tailWord_395502 prefixEnd_395502 60172629870997579349963 := by
  unfold tailWord_395502
  simp only [CollatzResearch.WordTrace]
  refine ⟨1803142876646409401133595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9616762008780850139379173 1803142876646409401133595)
  ·
    refine ⟨2704714314969614101700393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1803142876646409401133595 2704714314969614101700393)
    ·
      refine ⟨2028535736227210576275295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2704714314969614101700393 2028535736227210576275295)
      ·
        refine ⟨3042803604340815864412943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2028535736227210576275295 3042803604340815864412943)
        ·
          refine ⟨4564205406511223796619415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3042803604340815864412943 4564205406511223796619415)
          ·
            refine ⟨6846308109766835694929123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4564205406511223796619415 6846308109766835694929123)
            ·
              refine ⟨10269462164650253542393685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6846308109766835694929123 10269462164650253542393685)
              ·
                refine ⟨60172629870997579349963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10269462164650253542393685 60172629870997579349963)
                ·
                  rfl

theorem cell20_395502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 9].length) (baseStart_395502 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395502 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395502 prefixEnd_395502 := by exact prefixLift 395502
  have htrace : WordTrace (prefixWord ++ tailWord_395502) baseStart_395502 baseEnd_395502 := by
    simpa [prefixWord, tailWord_395502, baseEnd_395502] using wordTrace_append hprefix tailTrace_395502
  have hstable : (prefixWord ++ tailWord_395502).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395502).length < 2 ^ (prefixWord ++ tailWord_395502).sum := by decide
  have hdescent : baseEnd_395502 < baseStart_395502 := by decide
  rcases family_descends (prefixWord ++ tailWord_395502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395529 : List Nat := [1, 2, 1, 1, 3, 6, 1, 3, 2]
def baseStart_395529 : Nat := 118140960795 + 395529 * 2 ^ 59
def prefixEnd_395529 : Nat := 4983230072969 + 3 ^ 40 * 395529 * 2
def baseEnd_395529 : Nat := 180530213148700644149779

theorem tailTrace_395529 : CollatzResearch.WordTrace tailWord_395529 prefixEnd_395529 180530213148700644149779 := by
  unfold tailWord_395529
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426127784073458820301641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9617418522715639213534427 14426127784073458820301641)
  ·
    refine ⟨10819595838055094115226231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14426127784073458820301641 10819595838055094115226231)
    ·
      refine ⟨16229393757082641172839347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10819595838055094115226231 16229393757082641172839347)
      ·
        refine ⟨24344090635623961759259021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16229393757082641172839347 24344090635623961759259021)
        ·
          refine ⟨9129033988358985659722133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24344090635623961759259021 9129033988358985659722133)
          ·
            refine ⟨427923468204327452799475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 9129033988358985659722133 427923468204327452799475)
            ·
              refine ⟨641885202306491179199213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 427923468204327452799475 641885202306491179199213)
              ·
                refine ⟨240706950864934192199705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 641885202306491179199213 240706950864934192199705)
                ·
                  refine ⟨180530213148700644149779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240706950864934192199705 180530213148700644149779)
                  ·
                    rfl

theorem cell20_395529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_395529 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395529 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395529 prefixEnd_395529 := by exact prefixLift 395529
  have htrace : WordTrace (prefixWord ++ tailWord_395529) baseStart_395529 baseEnd_395529 := by
    simpa [prefixWord, tailWord_395529, baseEnd_395529] using wordTrace_append hprefix tailTrace_395529
  have hstable : (prefixWord ++ tailWord_395529).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395529).length < 2 ^ (prefixWord ++ tailWord_395529).sum := by decide
  have hdescent : baseEnd_395529 < baseStart_395529 := by decide
  rcases family_descends (prefixWord ++ tailWord_395529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395546 : List Nat := [3, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_395546 : Nat := 118140960795 + 395546 * 2 ^ 59
def prefixEnd_395546 : Nat := 4983230072969 + 3 ^ 40 * 395546 * 2
def baseEnd_395546 : Nat := 180537972411924140583043

theorem tailTrace_395546 : CollatzResearch.WordTrace tailWord_395546 prefixEnd_395546 180537972411924140583043 := by
  unfold tailWord_395546
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606686956252967680917623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9617831883341247149113661 3606686956252967680917623)
  ·
    refine ⟨5410030434379451521376435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606686956252967680917623 5410030434379451521376435)
    ·
      refine ⟨8115045651569177282064653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410030434379451521376435 8115045651569177282064653)
      ·
        refine ⟨3043142119338441480774245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8115045651569177282064653 3043142119338441480774245)
        ·
          refine ⟨570589147375957777645171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3043142119338441480774245 570589147375957777645171)
          ·
            refine ⟨855883721063936666467757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570589147375957777645171 855883721063936666467757)
            ·
              refine ⟨320956395398976249925409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 855883721063936666467757 320956395398976249925409)
              ·
                refine ⟨240717296549232187444057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 320956395398976249925409 240717296549232187444057)
                ·
                  refine ⟨180537972411924140583043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240717296549232187444057 180537972411924140583043)
                  ·
                    rfl

theorem cell20_395546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_395546 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395546 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395546 prefixEnd_395546 := by exact prefixLift 395546
  have htrace : WordTrace (prefixWord ++ tailWord_395546) baseStart_395546 baseEnd_395546 := by
    simpa [prefixWord, tailWord_395546, baseEnd_395546] using wordTrace_append hprefix tailTrace_395546
  have hstable : (prefixWord ++ tailWord_395546).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395546).length < 2 ^ (prefixWord ++ tailWord_395546).sum := by decide
  have hdescent : baseEnd_395546 < baseStart_395546 := by decide
  rcases family_descends (prefixWord ++ tailWord_395546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395547 : List Nat := [1, 1, 1, 1, 1, 1, 8, 1, 5]
def baseStart_395547 : Nat := 118140960795 + 395547 * 2 ^ 59
def prefixEnd_395547 : Nat := 4983230072969 + 3 ^ 40 * 395547 * 2
def baseEnd_395547 : Nat := 180538428839172581549705

theorem tailTrace_395547 : CollatzResearch.WordTrace tailWord_395547 prefixEnd_395547 180538428839172581549705 := by
  unfold tailWord_395547
  simp only [CollatzResearch.WordTrace]
  refine ⟨14426784298008247894456895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9617856198672165262971263 14426784298008247894456895)
  ·
    refine ⟨21640176447012371841685343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14426784298008247894456895 21640176447012371841685343)
    ·
      refine ⟨32460264670518557762528015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21640176447012371841685343 32460264670518557762528015)
      ·
        refine ⟨48690397005777836643792023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32460264670518557762528015 48690397005777836643792023)
        ·
          refine ⟨73035595508666754965688035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 48690397005777836643792023 73035595508666754965688035)
          ·
            refine ⟨109553393263000132448532053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 73035595508666754965688035 109553393263000132448532053)
            ·
              refine ⟨1283828827300782802131235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 109553393263000132448532053 1283828827300782802131235)
              ·
                refine ⟨1925743240951174203196853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1283828827300782802131235 1925743240951174203196853)
                ·
                  refine ⟨180538428839172581549705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1925743240951174203196853 180538428839172581549705)
                  ·
                    rfl

theorem cell20_395547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_395547 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395547 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395547 prefixEnd_395547 := by exact prefixLift 395547
  have htrace : WordTrace (prefixWord ++ tailWord_395547) baseStart_395547 baseEnd_395547 := by
    simpa [prefixWord, tailWord_395547, baseEnd_395547] using wordTrace_append hprefix tailTrace_395547
  have hstable : (prefixWord ++ tailWord_395547).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395547).length < 2 ^ (prefixWord ++ tailWord_395547).sum := by decide
  have hdescent : baseEnd_395547 < baseStart_395547 := by decide
  rcases family_descends (prefixWord ++ tailWord_395547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395557 : List Nat := [1, 3, 1, 2, 5, 1, 2, 5]
def baseStart_395557 : Nat := 118140960795 + 395557 * 2 ^ 59
def prefixEnd_395557 : Nat := 4983230072969 + 3 ^ 40 * 395557 * 2
def baseEnd_395557 : Nat := 60180997703885663738777

theorem tailTrace_395557 : CollatzResearch.WordTrace tailWord_395557 prefixEnd_395557 60180997703885663738777 := by
  unfold tailWord_395557
  simp only [CollatzResearch.WordTrace]
  refine ⟨14427149027972019602320925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9618099351981346401547283 14427149027972019602320925)
  ·
    refine ⟨5410180885489507350870347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14427149027972019602320925 5410180885489507350870347)
    ·
      refine ⟨8115271328234261026305521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410180885489507350870347 8115271328234261026305521)
      ·
        refine ⟨6086453496175695769729141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8115271328234261026305521 6086453496175695769729141)
        ·
          refine ⟨570605015266471478412107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6086453496175695769729141 570605015266471478412107)
          ·
            refine ⟨855907522899707217618161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570605015266471478412107 855907522899707217618161)
            ·
              refine ⟨641930642174780413213621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 855907522899707217618161 641930642174780413213621)
              ·
                refine ⟨60180997703885663738777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 641930642174780413213621 60180997703885663738777)
                ·
                  rfl

theorem cell20_395557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 2, 5].length) (baseStart_395557 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395557 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395557 prefixEnd_395557 := by exact prefixLift 395557
  have htrace : WordTrace (prefixWord ++ tailWord_395557) baseStart_395557 baseEnd_395557 := by
    simpa [prefixWord, tailWord_395557, baseEnd_395557] using wordTrace_append hprefix tailTrace_395557
  have hstable : (prefixWord ++ tailWord_395557).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395557).length < 2 ^ (prefixWord ++ tailWord_395557).sum := by decide
  have hdescent : baseEnd_395557 < baseStart_395557 := by decide
  rcases family_descends (prefixWord ++ tailWord_395557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395578 : List Nat := [3, 1, 1, 1, 4, 2, 2, 6]
def baseStart_395578 : Nat := 118140960795 + 395578 * 2 ^ 59
def prefixEnd_395578 : Nat := 4983230072969 + 3 ^ 40 * 395578 * 2
def baseEnd_395578 : Nat := 60184192694624750505415

theorem tailTrace_395578 : CollatzResearch.WordTrace tailWord_395578 prefixEnd_395578 60184192694624750505415 := by
  unfold tailWord_395578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3606978740223985047208847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9618609973930626792556925 3606978740223985047208847)
  ·
    refine ⟨5410468110335977570813271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3606978740223985047208847 5410468110335977570813271)
    ·
      refine ⟨8115702165503966356219907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5410468110335977570813271 8115702165503966356219907)
      ·
        refine ⟨12173553248255949534329861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8115702165503966356219907 12173553248255949534329861)
        ·
          refine ⟨2282541234047990537686849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12173553248255949534329861 2282541234047990537686849)
          ·
            refine ⟨1711905925535992903265137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2282541234047990537686849 1711905925535992903265137)
            ·
              refine ⟨1283929444151994677448853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1711905925535992903265137 1283929444151994677448853)
              ·
                refine ⟨60184192694624750505415, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1283929444151994677448853 60184192694624750505415)
                ·
                  rfl

theorem cell20_395578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_395578 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395578 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395578 prefixEnd_395578 := by exact prefixLift 395578
  have htrace : WordTrace (prefixWord ++ tailWord_395578) baseStart_395578 baseEnd_395578 := by
    simpa [prefixWord, tailWord_395578, baseEnd_395578] using wordTrace_append hprefix tailTrace_395578
  have hstable : (prefixWord ++ tailWord_395578).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395578).length < 2 ^ (prefixWord ++ tailWord_395578).sum := by decide
  have hdescent : baseEnd_395578 < baseStart_395578 := by decide
  rcases family_descends (prefixWord ++ tailWord_395578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395602 : List Nat := [3, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_395602 : Nat := 118140960795 + 395602 * 2 ^ 59
def prefixEnd_395602 : Nat := 4983230072969 + 3 ^ 40 * 395602 * 2
def baseEnd_395602 : Nat := 180563532337836834716147

theorem tailTrace_395602 : CollatzResearch.WordTrace tailWord_395602 prefixEnd_395602 180563532337836834716147 := by
  unfold tailWord_395602
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607197578202248071927265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9619193541872661525139373 3607197578202248071927265)
  ·
    refine ⟨2705398183651686053945449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3607197578202248071927265 2705398183651686053945449)
    ·
      refine ⟨2029048637738764540459087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2705398183651686053945449 2029048637738764540459087)
      ·
        refine ⟨3043572956608146810688631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2029048637738764540459087 3043572956608146810688631)
        ·
          refine ⟨4565359434912220216032947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3043572956608146810688631 4565359434912220216032947)
          ·
            refine ⟨6848039152368330324049421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4565359434912220216032947 6848039152368330324049421)
            ·
              refine ⟨2568014682138123871518533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6848039152368330324049421 2568014682138123871518533)
              ·
                refine ⟨481502752900898225909725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2568014682138123871518533 481502752900898225909725)
                ·
                  refine ⟨180563532337836834716147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481502752900898225909725 180563532337836834716147)
                  ·
                    rfl

theorem cell20_395602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_395602 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395602 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395602 prefixEnd_395602 := by exact prefixLift 395602
  have htrace : WordTrace (prefixWord ++ tailWord_395602) baseStart_395602 baseEnd_395602 := by
    simpa [prefixWord, tailWord_395602, baseEnd_395602] using wordTrace_append hprefix tailTrace_395602
  have hstable : (prefixWord ++ tailWord_395602).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395602).length < 2 ^ (prefixWord ++ tailWord_395602).sum := by decide
  have hdescent : baseEnd_395602 < baseStart_395602 := by decide
  rcases family_descends (prefixWord ++ tailWord_395602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395605 : List Nat := [1, 3, 2, 2, 4, 1, 1, 4, 2]
def baseStart_395605 : Nat := 118140960795 + 395605 * 2 ^ 59
def prefixEnd_395605 : Nat := 4983230072969 + 3 ^ 40 * 395605 * 2
def baseEnd_395605 : Nat := 180564901619582157616135

theorem tailTrace_395605 : CollatzResearch.WordTrace tailWord_395605 prefixEnd_395605 180564901619582157616135 := by
  unfold tailWord_395605
  simp only [CollatzResearch.WordTrace]
  refine ⟨14428899731798123800068269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9619266487865415866712179 14428899731798123800068269)
  ·
    refine ⟨5410837399424296425025601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14428899731798123800068269 5410837399424296425025601)
    ·
      refine ⟨4058128049568222318769201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5410837399424296425025601 4058128049568222318769201)
      ·
        refine ⟨3043596037176166739076901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4058128049568222318769201 3043596037176166739076901)
        ·
          refine ⟨570674256970531263576919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3043596037176166739076901 570674256970531263576919)
          ·
            refine ⟨856011385455796895365379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570674256970531263576919 856011385455796895365379)
            ·
              refine ⟨1284017078183695343048069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856011385455796895365379 1284017078183695343048069)
              ·
                refine ⟨240753202159442876821513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1284017078183695343048069 240753202159442876821513)
                ·
                  refine ⟨180564901619582157616135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240753202159442876821513 180564901619582157616135)
                  ·
                    rfl

theorem cell20_395605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 4, 2].length) (baseStart_395605 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395605 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395605 prefixEnd_395605 := by exact prefixLift 395605
  have htrace : WordTrace (prefixWord ++ tailWord_395605) baseStart_395605 baseEnd_395605 := by
    simpa [prefixWord, tailWord_395605, baseEnd_395605] using wordTrace_append hprefix tailTrace_395605
  have hstable : (prefixWord ++ tailWord_395605).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395605).length < 2 ^ (prefixWord ++ tailWord_395605).sum := by decide
  have hdescent : baseEnd_395605 < baseStart_395605 := by decide
  rcases family_descends (prefixWord ++ tailWord_395605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395626 : List Nat := [3, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_395626 : Nat := 118140960795 + 395626 * 2 ^ 59
def prefixEnd_395626 : Nat := 4983230072969 + 3 ^ 40 * 395626 * 2
def baseEnd_395626 : Nat := 180574486591799417916049

theorem tailTrace_395626 : CollatzResearch.WordTrace tailWord_395626 prefixEnd_395626 180574486591799417916049 := by
  unfold tailWord_395626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607416416180511096645683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9619777109814696257721821 3607416416180511096645683)
  ·
    refine ⟨5411124624270766644968525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3607416416180511096645683 5411124624270766644968525)
    ·
      refine ⟨2029171734101537491863197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5411124624270766644968525 2029171734101537491863197)
      ·
        refine ⟨760939400288076559448699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2029171734101537491863197 760939400288076559448699)
        ·
          refine ⟨1141409100432114839173049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 760939400288076559448699 1141409100432114839173049)
          ·
            refine ⟨856056825324086129379787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1141409100432114839173049 856056825324086129379787)
            ·
              refine ⟨1284085237986129194069681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 856056825324086129379787 1284085237986129194069681)
              ·
                refine ⟨963063928489596895552261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1284085237986129194069681 963063928489596895552261)
                ·
                  refine ⟨180574486591799417916049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963063928489596895552261 180574486591799417916049)
                  ·
                    rfl

theorem cell20_395626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_395626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395626 prefixEnd_395626 := by exact prefixLift 395626
  have htrace : WordTrace (prefixWord ++ tailWord_395626) baseStart_395626 baseEnd_395626 := by
    simpa [prefixWord, tailWord_395626, baseEnd_395626] using wordTrace_append hprefix tailTrace_395626
  have hstable : (prefixWord ++ tailWord_395626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395626).length < 2 ^ (prefixWord ++ tailWord_395626).sum := by decide
  have hdescent : baseEnd_395626 < baseStart_395626 := by decide
  rcases family_descends (prefixWord ++ tailWord_395626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395650 : List Nat := [3, 4, 2, 1, 2, 1, 7]
def baseStart_395650 : Nat := 118140960795 + 395650 * 2 ^ 59
def prefixEnd_395650 : Nat := 4983230072969 + 3 ^ 40 * 395650 * 2
def baseEnd_395650 : Nat := 20065048982862444568439

theorem tailTrace_395650 : CollatzResearch.WordTrace tailWord_395650 prefixEnd_395650 20065048982862444568439 := by
  unfold tailWord_395650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3607635254158774121364101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9620360677756730990304269 3607635254158774121364101)
  ·
    refine ⟨676431610154770147755769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3607635254158774121364101 676431610154770147755769)
    ·
      refine ⟨507323707616077610816827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 676431610154770147755769 507323707616077610816827)
      ·
        refine ⟨760985561424116416225241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507323707616077610816827 760985561424116416225241)
        ·
          refine ⟨570739171068087312168931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 760985561424116416225241 570739171068087312168931)
          ·
            refine ⟨856108756602130968253397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570739171068087312168931 856108756602130968253397)
            ·
              refine ⟨20065048982862444568439, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 856108756602130968253397 20065048982862444568439)
              ·
                rfl

theorem cell20_395650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 1, 7].length) (baseStart_395650 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395650 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395650 prefixEnd_395650 := by exact prefixLift 395650
  have htrace : WordTrace (prefixWord ++ tailWord_395650) baseStart_395650 baseEnd_395650 := by
    simpa [prefixWord, tailWord_395650, baseEnd_395650] using wordTrace_append hprefix tailTrace_395650
  have hstable : (prefixWord ++ tailWord_395650).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395650).length < 2 ^ (prefixWord ++ tailWord_395650).sum := by decide
  have hdescent : baseEnd_395650 < baseStart_395650 := by decide
  rcases family_descends (prefixWord ++ tailWord_395650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395657 : List Nat := [1, 2, 1, 1, 6, 3, 1, 2, 3]
def baseStart_395657 : Nat := 118140960795 + 395657 * 2 ^ 59
def prefixEnd_395657 : Nat := 4983230072969 + 3 ^ 40 * 395657 * 2
def baseEnd_395657 : Nat := 180588635836501087882589

theorem tailTrace_395657 : CollatzResearch.WordTrace tailWord_395657 prefixEnd_395657 180588635836501087882589 := by
  unfold tailWord_395657
  simp only [CollatzResearch.WordTrace]
  refine ⟨14430796327609736680961225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9620530885073157787307483 14430796327609736680961225)
  ·
    refine ⟨10823097245707302510720919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14430796327609736680961225 10823097245707302510720919)
    ·
      refine ⟨16234645868560953766081379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10823097245707302510720919 16234645868560953766081379)
      ·
        refine ⟨24351968802841430649122069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16234645868560953766081379 24351968802841430649122069)
        ·
          refine ⟨1141498537633192061677597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 24351968802841430649122069 1141498537633192061677597)
          ·
            refine ⟨428061951612447023129099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1141498537633192061677597 428061951612447023129099)
            ·
              refine ⟨642092927418670534693649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428061951612447023129099 642092927418670534693649)
              ·
                refine ⟨481569695564002901020237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 642092927418670534693649 481569695564002901020237)
                ·
                  refine ⟨180588635836501087882589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481569695564002901020237 180588635836501087882589)
                  ·
                    rfl

theorem cell20_395657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 1, 2, 3].length) (baseStart_395657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395657 prefixEnd_395657 := by exact prefixLift 395657
  have htrace : WordTrace (prefixWord ++ tailWord_395657) baseStart_395657 baseEnd_395657 := by
    simpa [prefixWord, tailWord_395657, baseEnd_395657] using wordTrace_append hprefix tailTrace_395657
  have hstable : (prefixWord ++ tailWord_395657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395657).length < 2 ^ (prefixWord ++ tailWord_395657).sum := by decide
  have hdescent : baseEnd_395657 < baseStart_395657 := by decide
  rcases family_descends (prefixWord ++ tailWord_395657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395688 : List Nat := [2, 1, 6, 1, 1, 1, 4, 4]
def baseStart_395688 : Nat := 118140960795 + 395688 * 2 ^ 59
def prefixEnd_395688 : Nat := 4983230072969 + 3 ^ 40 * 395688 * 2
def baseEnd_395688 : Nat := 60200928360400919283043

theorem tailTrace_395688 : CollatzResearch.WordTrace tailWord_395688 prefixEnd_395688 60200928360400919283043 := by
  unfold tailWord_395688
  simp only [CollatzResearch.WordTrace]
  refine ⟨7215963495248714487669859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9621284660331619316893145 7215963495248714487669859)
  ·
    refine ⟨10823945242873071731504789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7215963495248714487669859 10823945242873071731504789)
    ·
      refine ⟨507372433259675237414287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 10823945242873071731504789 507372433259675237414287)
      ·
        refine ⟨761058649889512856121431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 507372433259675237414287 761058649889512856121431)
        ·
          refine ⟨1141587974834269284182147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 761058649889512856121431 1141587974834269284182147)
          ·
            refine ⟨1712381962251403926273221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1141587974834269284182147 1712381962251403926273221)
            ·
              refine ⟨321071617922138236176229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1712381962251403926273221 321071617922138236176229)
              ·
                refine ⟨60200928360400919283043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321071617922138236176229 60200928360400919283043)
                ·
                  rfl

theorem cell20_395688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 4, 4].length) (baseStart_395688 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395688 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395688 prefixEnd_395688 := by exact prefixLift 395688
  have htrace : WordTrace (prefixWord ++ tailWord_395688) baseStart_395688 baseEnd_395688 := by
    simpa [prefixWord, tailWord_395688, baseEnd_395688] using wordTrace_append hprefix tailTrace_395688
  have hstable : (prefixWord ++ tailWord_395688).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395688).length < 2 ^ (prefixWord ++ tailWord_395688).sum := by decide
  have hdescent : baseEnd_395688 < baseStart_395688 := by decide
  rcases family_descends (prefixWord ++ tailWord_395688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395706 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 6]
def baseStart_395706 : Nat := 118140960795 + 395706 * 2 ^ 59
def prefixEnd_395706 : Nat := 4983230072969 + 3 ^ 40 * 395706 * 2
def baseEnd_395706 : Nat := 180611000771674695249055

theorem tailTrace_395706 : CollatzResearch.WordTrace tailWord_395706 prefixEnd_395706 180611000771674695249055 := by
  unfold tailWord_395706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3608145876108054512373743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9621722336288145366329981 3608145876108054512373743)
  ·
    refine ⟨5412218814162081768560615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3608145876108054512373743 5412218814162081768560615)
    ·
      refine ⟨8118328221243122652840923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5412218814162081768560615 8118328221243122652840923)
      ·
        refine ⟨12177492331864683979261385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8118328221243122652840923 12177492331864683979261385)
        ·
          refine ⟨9133119248898512984446039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12177492331864683979261385 9133119248898512984446039)
          ·
            refine ⟨13699678873347769476669059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9133119248898512984446039 13699678873347769476669059)
            ·
              refine ⟨20549518310021654215003589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13699678873347769476669059 20549518310021654215003589)
              ·
                refine ⟨3853034683129060165313173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 20549518310021654215003589 3853034683129060165313173)
                ·
                  refine ⟨180611000771674695249055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3853034683129060165313173 180611000771674695249055)
                  ·
                    rfl

theorem cell20_395706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 6].length) (baseStart_395706 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395706 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395706 prefixEnd_395706 := by exact prefixLift 395706
  have htrace : WordTrace (prefixWord ++ tailWord_395706) baseStart_395706 baseEnd_395706 := by
    simpa [prefixWord, tailWord_395706, baseEnd_395706] using wordTrace_append hprefix tailTrace_395706
  have hstable : (prefixWord ++ tailWord_395706).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395706).length < 2 ^ (prefixWord ++ tailWord_395706).sum := by decide
  have hdescent : baseEnd_395706 < baseStart_395706 := by decide
  rcases family_descends (prefixWord ++ tailWord_395706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395719 : List Nat := [1, 1, 4, 1, 1, 5, 3, 2, 2]
def baseStart_395719 : Nat := 118140960795 + 395719 * 2 ^ 59
def prefixEnd_395719 : Nat := 4983230072969 + 3 ^ 40 * 395719 * 2
def baseEnd_395719 : Nat := 180616934325904427815669

theorem tailTrace_395719 : CollatzResearch.WordTrace tailWord_395719 prefixEnd_395719 180616934325904427815669 := by
  unfold tailWord_395719
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433057653385121269718211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9622038435590080846478807 14433057653385121269718211)
  ·
    refine ⟨21649586480077681904577317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14433057653385121269718211 21649586480077681904577317)
    ·
      refine ⟨4059297465014565357108247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21649586480077681904577317 4059297465014565357108247)
      ·
        refine ⟨6088946197521848035662371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4059297465014565357108247 6088946197521848035662371)
        ·
          refine ⟨9133419296282772053493557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6088946197521848035662371 9133419296282772053493557)
          ·
            refine ⟨856258059026509880015021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9133419296282772053493557 856258059026509880015021)
            ·
              refine ⟨321096772134941205005633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856258059026509880015021 321096772134941205005633)
              ·
                refine ⟨240822579101205903754225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321096772134941205005633 240822579101205903754225)
                ·
                  refine ⟨180616934325904427815669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240822579101205903754225 180616934325904427815669)
                  ·
                    rfl

theorem cell20_395719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 3, 2, 2].length) (baseStart_395719 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395719 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395719 prefixEnd_395719 := by exact prefixLift 395719
  have htrace : WordTrace (prefixWord ++ tailWord_395719) baseStart_395719 baseEnd_395719 := by
    simpa [prefixWord, tailWord_395719, baseEnd_395719] using wordTrace_append hprefix tailTrace_395719
  have hstable : (prefixWord ++ tailWord_395719).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395719).length < 2 ^ (prefixWord ++ tailWord_395719).sum := by decide
  have hdescent : baseEnd_395719 < baseStart_395719 := by decide
  rcases family_descends (prefixWord ++ tailWord_395719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395733 : List Nat := [1, 3, 2, 3, 1, 2, 4, 1, 3]
def baseStart_395733 : Nat := 118140960795 + 395733 * 2 ^ 59
def prefixEnd_395733 : Nat := 4983230072969 + 3 ^ 40 * 395733 * 2
def baseEnd_395733 : Nat := 180623324307382601348945

theorem tailTrace_395733 : CollatzResearch.WordTrace tailWord_395733 prefixEnd_395733 180623324307382601348945 := by
  unfold tailWord_395733
  simp only [CollatzResearch.WordTrace]
  refine ⟨14433568275334401660727853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9622378850222934440485235 14433568275334401660727853)
  ·
    refine ⟨5412588103250400622772945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14433568275334401660727853 5412588103250400622772945)
    ·
      refine ⟨4059441077437800467079709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5412588103250400622772945 4059441077437800467079709)
      ·
        refine ⟨1522290404039175175154891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4059441077437800467079709 1522290404039175175154891)
        ·
          refine ⟨2283435606058762762732337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1522290404039175175154891 2283435606058762762732337)
          ·
            refine ⟨1712576704544072072049253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2283435606058762762732337 1712576704544072072049253)
            ·
              refine ⟨321108132102013513509235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1712576704544072072049253 321108132102013513509235)
              ·
                refine ⟨481662198153020270263853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321108132102013513509235 481662198153020270263853)
                ·
                  refine ⟨180623324307382601348945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481662198153020270263853 180623324307382601348945)
                  ·
                    rfl

theorem cell20_395733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 4, 1, 3].length) (baseStart_395733 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395733 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395733 prefixEnd_395733 := by exact prefixLift 395733
  have htrace : WordTrace (prefixWord ++ tailWord_395733) baseStart_395733 baseEnd_395733 := by
    simpa [prefixWord, tailWord_395733, baseEnd_395733] using wordTrace_append hprefix tailTrace_395733
  have hstable : (prefixWord ++ tailWord_395733).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395733).length < 2 ^ (prefixWord ++ tailWord_395733).sum := by decide
  have hdescent : baseEnd_395733 < baseStart_395733 := by decide
  rcases family_descends (prefixWord ++ tailWord_395733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395744 : List Nat := [2, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_395744 : Nat := 118140960795 + 395744 * 2 ^ 59
def prefixEnd_395744 : Nat := 4983230072969 + 3 ^ 40 * 395744 * 2
def baseEnd_395744 : Nat := 180628345007115451982233

theorem tailTrace_395744 : CollatzResearch.WordTrace tailWord_395744 prefixEnd_395744 180628345007115451982233 := by
  unfold tailWord_395744
  simp only [CollatzResearch.WordTrace]
  refine ⟨7216984739147275269689143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9622646318863033692918857 7216984739147275269689143)
  ·
    refine ⟨10825477108720912904533715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7216984739147275269689143 10825477108720912904533715)
    ·
      refine ⟨16238215663081369356800573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10825477108720912904533715 16238215663081369356800573)
      ·
        refine ⟨6089330873655513508800215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16238215663081369356800573 6089330873655513508800215)
        ·
          refine ⟨9133996310483270263200323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6089330873655513508800215 9133996310483270263200323)
          ·
            refine ⟨13700994465724905394800485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9133996310483270263200323 13700994465724905394800485)
            ·
              refine ⟨2568936462323419761525091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 13700994465724905394800485 2568936462323419761525091)
              ·
                refine ⟨3853404693485129642287637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2568936462323419761525091 3853404693485129642287637)
                ·
                  refine ⟨180628345007115451982233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 3853404693485129642287637 180628345007115451982233)
                  ·
                    rfl

theorem cell20_395744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_395744 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395744 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395744 prefixEnd_395744 := by exact prefixLift 395744
  have htrace : WordTrace (prefixWord ++ tailWord_395744) baseStart_395744 baseEnd_395744 := by
    simpa [prefixWord, tailWord_395744, baseEnd_395744] using wordTrace_append hprefix tailTrace_395744
  have hstable : (prefixWord ++ tailWord_395744).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395744).length < 2 ^ (prefixWord ++ tailWord_395744).sum := by decide
  have hdescent : baseEnd_395744 < baseStart_395744 := by decide
  rcases family_descends (prefixWord ++ tailWord_395744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395812 : List Nat := [2, 3, 1, 5, 1, 1, 2, 3, 2]
def baseStart_395812 : Nat := 118140960795 + 395812 * 2 ^ 59
def prefixEnd_395812 : Nat := 4983230072969 + 3 ^ 40 * 395812 * 2
def baseEnd_395812 : Nat := 180659382060009437715289

theorem tailTrace_395812 : CollatzResearch.WordTrace tailWord_395812 prefixEnd_395812 180659382060009437715289 := by
  unfold tailWord_395812
  simp only [CollatzResearch.WordTrace]
  refine ⟨7218224821024099076426845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9624299761365465435235793 7218224821024099076426845)
  ·
    refine ⟨2706834307884037153660067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7218224821024099076426845 2706834307884037153660067)
    ·
      refine ⟨4060251461826055730490101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2706834307884037153660067 4060251461826055730490101)
      ·
        refine ⟨380648574546192724733447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4060251461826055730490101 380648574546192724733447)
        ·
          refine ⟨570972861819289087100171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380648574546192724733447 570972861819289087100171)
          ·
            refine ⟨856459292728933630650257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 570972861819289087100171 856459292728933630650257)
            ·
              refine ⟨642344469546700222987693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 856459292728933630650257 642344469546700222987693)
              ·
                refine ⟨240879176080012583620385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 642344469546700222987693 240879176080012583620385)
                ·
                  refine ⟨180659382060009437715289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240879176080012583620385 180659382060009437715289)
                  ·
                    rfl

theorem cell20_395812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 1, 2, 3, 2].length) (baseStart_395812 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395812 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395812 prefixEnd_395812 := by exact prefixLift 395812
  have htrace : WordTrace (prefixWord ++ tailWord_395812) baseStart_395812 baseEnd_395812 := by
    simpa [prefixWord, tailWord_395812, baseEnd_395812] using wordTrace_append hprefix tailTrace_395812
  have hstable : (prefixWord ++ tailWord_395812).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395812).length < 2 ^ (prefixWord ++ tailWord_395812).sum := by decide
  have hdescent : baseEnd_395812 < baseStart_395812 := by decide
  rcases family_descends (prefixWord ++ tailWord_395812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395827 : List Nat := [1, 1, 1, 2, 4, 2, 9]
def baseStart_395827 : Nat := 118140960795 + 395827 * 2 ^ 59
def prefixEnd_395827 : Nat := 4983230072969 + 3 ^ 40 * 395827 * 2
def baseEnd_395827 : Nat := 20074025385415116912803

theorem tailTrace_395827 : CollatzResearch.WordTrace tailWord_395827 prefixEnd_395827 20074025385415116912803 := by
  unfold tailWord_395827
  simp only [CollatzResearch.WordTrace]
  refine ⟨14436996736993855714649735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9624664491329237143099823 14436996736993855714649735)
  ·
    refine ⟨21655495105490783571974603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14436996736993855714649735 21655495105490783571974603)
    ·
      refine ⟨32483242658236175357961905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21655495105490783571974603 32483242658236175357961905)
      ·
        refine ⟨24362431993677131518471429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 32483242658236175357961905 24362431993677131518471429)
        ·
          refine ⟨4567955998814462159713393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 24362431993677131518471429 4567955998814462159713393)
          ·
            refine ⟨3425966999110846619785045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4567955998814462159713393 3425966999110846619785045)
            ·
              refine ⟨20074025385415116912803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 3425966999110846619785045 20074025385415116912803)
              ·
                rfl

theorem cell20_395827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 9].length) (baseStart_395827 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395827 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395827 prefixEnd_395827 := by exact prefixLift 395827
  have htrace : WordTrace (prefixWord ++ tailWord_395827) baseStart_395827 baseEnd_395827 := by
    simpa [prefixWord, tailWord_395827, baseEnd_395827] using wordTrace_append hprefix tailTrace_395827
  have hstable : (prefixWord ++ tailWord_395827).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395827).length < 2 ^ (prefixWord ++ tailWord_395827).sum := by decide
  have hdescent : baseEnd_395827 < baseStart_395827 := by decide
  rcases family_descends (prefixWord ++ tailWord_395827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395837 : List Nat := [1, 4, 1, 3, 2, 1, 1, 3, 4]
def baseStart_395837 : Nat := 118140960795 + 395837 * 2 ^ 59
def prefixEnd_395837 : Nat := 4983230072969 + 3 ^ 40 * 395837 * 2
def baseEnd_395837 : Nat := 180670792741220461881853

theorem tailTrace_395837 : CollatzResearch.WordTrace tailWord_395837 prefixEnd_395837 180670792741220461881853 := by
  unfold tailWord_395837
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437361466957627422513765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9624907644638418281675843 14437361466957627422513765)
  ·
    refine ⟨2707005275054555141721331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14437361466957627422513765 2707005275054555141721331)
    ·
      refine ⟨4060507912581832712581997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2707005275054555141721331 4060507912581832712581997)
      ·
        refine ⟨1522690467218187267218249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4060507912581832712581997 1522690467218187267218249)
        ·
          refine ⟨1142017850413640450413687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1522690467218187267218249 1142017850413640450413687)
          ·
            refine ⟨1713026775620460675620531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1142017850413640450413687 1713026775620460675620531)
            ·
              refine ⟨2569540163430691013430797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1713026775620460675620531 2569540163430691013430797)
              ·
                refine ⟨963577561286509130036549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2569540163430691013430797 963577561286509130036549)
                ·
                  refine ⟨180670792741220461881853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 963577561286509130036549 180670792741220461881853)
                  ·
                    rfl

theorem cell20_395837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 1, 3, 4].length) (baseStart_395837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395837 prefixEnd_395837 := by exact prefixLift 395837
  have htrace : WordTrace (prefixWord ++ tailWord_395837) baseStart_395837 baseEnd_395837 := by
    simpa [prefixWord, tailWord_395837, baseEnd_395837] using wordTrace_append hprefix tailTrace_395837
  have hstable : (prefixWord ++ tailWord_395837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395837).length < 2 ^ (prefixWord ++ tailWord_395837).sum := by decide
  have hdescent : baseEnd_395837 < baseStart_395837 := by decide
  rcases family_descends (prefixWord ++ tailWord_395837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395847 : List Nat := [1, 1, 4, 1, 4, 2, 3, 1, 3]
def baseStart_395847 : Nat := 118140960795 + 395847 * 2 ^ 59
def prefixEnd_395847 : Nat := 4983230072969 + 3 ^ 40 * 395847 * 2
def baseEnd_395847 : Nat := 180675357013704871548479

theorem tailTrace_395847 : CollatzResearch.WordTrace tailWord_395847 prefixEnd_395847 180675357013704871548479 := by
  unfold tailWord_395847
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437726196921399130377795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9625150797947599420251863 14437726196921399130377795)
  ·
    refine ⟨21656589295382098695566693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437726196921399130377795 21656589295382098695566693)
    ·
      refine ⟨4060610492884143505418755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21656589295382098695566693 4060610492884143505418755)
      ·
        refine ⟨6090915739326215258128133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4060610492884143505418755 6090915739326215258128133)
        ·
          refine ⟨1142046701123665360899025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6090915739326215258128133 1142046701123665360899025)
          ·
            refine ⟨856535025842749020674269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1142046701123665360899025 856535025842749020674269)
            ·
              refine ⟨321200634691030882752851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 856535025842749020674269 321200634691030882752851)
              ·
                refine ⟨481800952036546324129277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321200634691030882752851 481800952036546324129277)
                ·
                  refine ⟨180675357013704871548479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481800952036546324129277 180675357013704871548479)
                  ·
                    rfl

theorem cell20_395847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 3, 1, 3].length) (baseStart_395847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395847 prefixEnd_395847 := by exact prefixLift 395847
  have htrace : WordTrace (prefixWord ++ tailWord_395847) baseStart_395847 baseEnd_395847 := by
    simpa [prefixWord, tailWord_395847, baseEnd_395847] using wordTrace_append hprefix tailTrace_395847
  have hstable : (prefixWord ++ tailWord_395847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395847).length < 2 ^ (prefixWord ++ tailWord_395847).sum := by decide
  have hdescent : baseEnd_395847 < baseStart_395847 := by decide
  rcases family_descends (prefixWord ++ tailWord_395847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395851 : List Nat := [1, 1, 1, 1, 3, 1, 4, 5, 3]
def baseStart_395851 : Nat := 118140960795 + 395851 * 2 ^ 59
def prefixEnd_395851 : Nat := 4983230072969 + 3 ^ 40 * 395851 * 2
def baseEnd_395851 : Nat := 180677182722698635415129

theorem tailTrace_395851 : CollatzResearch.WordTrace tailWord_395851 prefixEnd_395851 180677182722698635415129 := by
  unfold tailWord_395851
  simp only [CollatzResearch.WordTrace]
  refine ⟨14437872088906907813523407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9625248059271271875682271 14437872088906907813523407)
  ·
    refine ⟨21656808133360361720285111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14437872088906907813523407 21656808133360361720285111)
    ·
      refine ⟨32485212200040542580427667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 21656808133360361720285111 32485212200040542580427667)
      ·
        refine ⟨48727818300060813870641501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 32485212200040542580427667 48727818300060813870641501)
        ·
          refine ⟨18272931862522805201490563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 48727818300060813870641501 18272931862522805201490563)
          ·
            refine ⟨27409397793784207802235845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 18272931862522805201490563 27409397793784207802235845)
            ·
              refine ⟨5139262086334538962919221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 27409397793784207802235845 5139262086334538962919221)
              ·
                refine ⟨481805820593863027773677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5139262086334538962919221 481805820593863027773677)
                ·
                  refine ⟨180677182722698635415129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 481805820593863027773677 180677182722698635415129)
                  ·
                    rfl

theorem cell20_395851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 5, 3].length) (baseStart_395851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395851 prefixEnd_395851 := by exact prefixLift 395851
  have htrace : WordTrace (prefixWord ++ tailWord_395851) baseStart_395851 baseEnd_395851 := by
    simpa [prefixWord, tailWord_395851, baseEnd_395851] using wordTrace_append hprefix tailTrace_395851
  have hstable : (prefixWord ++ tailWord_395851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395851).length < 2 ^ (prefixWord ++ tailWord_395851).sum := by decide
  have hdescent : baseEnd_395851 < baseStart_395851 := by decide
  rcases family_descends (prefixWord ++ tailWord_395851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_395943 : List Nat := [1, 1, 6, 3, 1, 2, 2, 2, 2]
def baseStart_395943 : Nat := 118140960795 + 395943 * 2 ^ 59
def prefixEnd_395943 : Nat := 4983230072969 + 3 ^ 40 * 395943 * 2
def baseEnd_395943 : Nat := 180719174029555204348087

theorem tailTrace_395943 : CollatzResearch.WordTrace tailWord_395943 prefixEnd_395943 180719174029555204348087 := by
  unfold tailWord_395943
  simp only [CollatzResearch.WordTrace]
  refine ⟨14441227604573607525872483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9627485069715738350581655 14441227604573607525872483)
  ·
    refine ⟨21661841406860411288808725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14441227604573607525872483 21661841406860411288808725)
    ·
      refine ⟨1015398815946581779162909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 21661841406860411288808725 1015398815946581779162909)
      ·
        refine ⟨380774555979968167186091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1015398815946581779162909 380774555979968167186091)
        ·
          refine ⟨571161833969952250779137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380774555979968167186091 571161833969952250779137)
          ·
            refine ⟨428371375477464188084353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571161833969952250779137 428371375477464188084353)
            ·
              refine ⟨321278531608098141063265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428371375477464188084353 321278531608098141063265)
              ·
                refine ⟨240958898706073605797449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321278531608098141063265 240958898706073605797449)
                ·
                  refine ⟨180719174029555204348087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 240958898706073605797449 180719174029555204348087)
                  ·
                    rfl

theorem cell20_395943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 2, 2, 2, 2].length) (baseStart_395943 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_395943 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_395943 prefixEnd_395943 := by exact prefixLift 395943
  have htrace : WordTrace (prefixWord ++ tailWord_395943) baseStart_395943 baseEnd_395943 := by
    simpa [prefixWord, tailWord_395943, baseEnd_395943] using wordTrace_append hprefix tailTrace_395943
  have hstable : (prefixWord ++ tailWord_395943).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_395943).length < 2 ^ (prefixWord ++ tailWord_395943).sum := by decide
  have hdescent : baseEnd_395943 < baseStart_395943 := by decide
  rcases family_descends (prefixWord ++ tailWord_395943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396017 : List Nat := [1, 2, 2, 2, 2, 2, 2, 7]
def baseStart_396017 : Nat := 118140960795 + 396017 * 2 ^ 59
def prefixEnd_396017 : Nat := 4983230072969 + 3 ^ 40 * 396017 * 2
def baseEnd_396017 : Nat := 60250983215313278627039

theorem tailTrace_396017 : CollatzResearch.WordTrace tailWord_396017 prefixEnd_396017 60250983215313278627039 := by
  unfold tailWord_396017
  simp only [CollatzResearch.WordTrace]
  refine ⟨14443926606305518164066305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9629284404203678776044203 14443926606305518164066305)
  ·
    refine ⟨10832944954729138623049729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14443926606305518164066305 10832944954729138623049729)
    ·
      refine ⟨8124708716046853967287297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10832944954729138623049729 8124708716046853967287297)
      ·
        refine ⟨6093531537035140475465473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8124708716046853967287297 6093531537035140475465473)
        ·
          refine ⟨4570148652776355356599105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6093531537035140475465473 4570148652776355356599105)
          ·
            refine ⟨3427611489582266517449329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4570148652776355356599105 3427611489582266517449329)
            ·
              refine ⟨2570708617186699888086997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3427611489582266517449329 2570708617186699888086997)
              ·
                refine ⟨60250983215313278627039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2570708617186699888086997 60250983215313278627039)
                ·
                  rfl

theorem cell20_396017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 7].length) (baseStart_396017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396017 prefixEnd_396017 := by exact prefixLift 396017
  have htrace : WordTrace (prefixWord ++ tailWord_396017) baseStart_396017 baseEnd_396017 := by
    simpa [prefixWord, tailWord_396017, baseEnd_396017] using wordTrace_append hprefix tailTrace_396017
  have hstable : (prefixWord ++ tailWord_396017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396017).length < 2 ^ (prefixWord ++ tailWord_396017).sum := by decide
  have hdescent : baseEnd_396017 < baseStart_396017 := by decide
  rcases family_descends (prefixWord ++ tailWord_396017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396030 : List Nat := [4, 2, 2, 1, 2, 3, 2, 4]
def baseStart_396030 : Nat := 118140960795 + 396030 * 2 ^ 59
def prefixEnd_396030 : Nat := 4983230072969 + 3 ^ 40 * 396030 * 2
def baseEnd_396030 : Nat := 60252961066723189482577

theorem tailTrace_396030 : CollatzResearch.WordTrace tailWord_396030 prefixEnd_396030 60252961066723189482577 := by
  unfold tailWord_396030
  simp only [CollatzResearch.WordTrace]
  refine ⟨1805550094407302673036193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 9629600503505614256193029 1805550094407302673036193)
  ·
    refine ⟨1354162570805477004777145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1805550094407302673036193 1354162570805477004777145)
    ·
      refine ⟨1015621928104107753582859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1354162570805477004777145 1015621928104107753582859)
      ·
        refine ⟨1523432892156161630374289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015621928104107753582859 1523432892156161630374289)
        ·
          refine ⟨1142574669117121222780717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1523432892156161630374289 1142574669117121222780717)
          ·
            refine ⟨428465500918920458542769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1142574669117121222780717 428465500918920458542769)
            ·
              refine ⟨321349125689190343907077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428465500918920458542769 321349125689190343907077)
              ·
                refine ⟨60252961066723189482577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321349125689190343907077 60252961066723189482577)
                ·
                  rfl

theorem cell20_396030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 3, 2, 4].length) (baseStart_396030 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396030 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396030 prefixEnd_396030 := by exact prefixLift 396030
  have htrace : WordTrace (prefixWord ++ tailWord_396030) baseStart_396030 baseEnd_396030 := by
    simpa [prefixWord, tailWord_396030, baseEnd_396030] using wordTrace_append hprefix tailTrace_396030
  have hstable : (prefixWord ++ tailWord_396030).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396030).length < 2 ^ (prefixWord ++ tailWord_396030).sum := by decide
  have hdescent : baseEnd_396030 < baseStart_396030 := by decide
  rcases family_descends (prefixWord ++ tailWord_396030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396061 : List Nat := [1, 4, 2, 4, 1, 2, 1, 1, 4]
def baseStart_396061 : Nat := 118140960795 + 396061 * 2 ^ 59
def prefixEnd_396061 : Nat := 4983230072969 + 3 ^ 40 * 396061 * 2
def baseEnd_396061 : Nat := 180773032444871238414271

theorem tailTrace_396061 : CollatzResearch.WordTrace tailWord_396061 prefixEnd_396061 180773032444871238414271 := by
  unfold tailWord_396061
  simp only [CollatzResearch.WordTrace]
  refine ⟨14445531418146113678668037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9630354278764075785778691 14445531418146113678668037)
  ·
    refine ⟨2708537140902396314750257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14445531418146113678668037 2708537140902396314750257)
    ·
      refine ⟨2031402855676797236062693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2708537140902396314750257 2031402855676797236062693)
      ·
        refine ⟨380888035439399481761755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2031402855676797236062693 380888035439399481761755)
        ·
          refine ⟨571332053159099222642633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 380888035439399481761755 571332053159099222642633)
          ·
            refine ⟨428499039869324416981975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571332053159099222642633 428499039869324416981975)
            ·
              refine ⟨642748559803986625472963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428499039869324416981975 642748559803986625472963)
              ·
                refine ⟨964122839705979938209445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 642748559803986625472963 964122839705979938209445)
                ·
                  refine ⟨180773032444871238414271, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964122839705979938209445 180773032444871238414271)
                  ·
                    rfl

theorem cell20_396061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 2, 1, 1, 4].length) (baseStart_396061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396061 prefixEnd_396061 := by exact prefixLift 396061
  have htrace : WordTrace (prefixWord ++ tailWord_396061) baseStart_396061 baseEnd_396061 := by
    simpa [prefixWord, tailWord_396061, baseEnd_396061] using wordTrace_append hprefix tailTrace_396061
  have hstable : (prefixWord ++ tailWord_396061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396061).length < 2 ^ (prefixWord ++ tailWord_396061).sum := by decide
  have hdescent : baseEnd_396061 < baseStart_396061 := by decide
  rcases family_descends (prefixWord ++ tailWord_396061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396072 : List Nat := [2, 1, 5, 1, 1, 1, 4, 5]
def baseStart_396072 : Nat := 118140960795 + 396072 * 2 ^ 59
def prefixEnd_396072 : Nat := 4983230072969 + 3 ^ 40 * 396072 * 2
def baseEnd_396072 : Nat := 60259351048201363015853

theorem tailTrace_396072 : CollatzResearch.WordTrace tailWord_396072 prefixEnd_396072 60259351048201363015853 := by
  unfold tailWord_396072
  simp only [CollatzResearch.WordTrace]
  refine ⟨7222966310553131278659235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9630621747404175038212313 7222966310553131278659235)
  ·
    refine ⟨10834449465829696917988853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7222966310553131278659235 10834449465829696917988853)
    ·
      refine ⟨1015729637421534086061455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 10834449465829696917988853 1015729637421534086061455)
      ·
        refine ⟨1523594456132301129092183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1015729637421534086061455 1523594456132301129092183)
        ·
          refine ⟨2285391684198451693638275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1523594456132301129092183 2285391684198451693638275)
          ·
            refine ⟨3428087526297677540457413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2285391684198451693638275 3428087526297677540457413)
            ·
              refine ⟨642766411180814538835765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3428087526297677540457413 642766411180814538835765)
              ·
                refine ⟨60259351048201363015853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 642766411180814538835765 60259351048201363015853)
                ·
                  rfl

theorem cell20_396072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 4, 5].length) (baseStart_396072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396072 prefixEnd_396072 := by exact prefixLift 396072
  have htrace : WordTrace (prefixWord ++ tailWord_396072) baseStart_396072 baseEnd_396072 := by
    simpa [prefixWord, tailWord_396072, baseEnd_396072] using wordTrace_append hprefix tailTrace_396072
  have hstable : (prefixWord ++ tailWord_396072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396072).length < 2 ^ (prefixWord ++ tailWord_396072).sum := by decide
  have hdescent : baseEnd_396072 < baseStart_396072 := by decide
  rcases family_descends (prefixWord ++ tailWord_396072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396103 : List Nat := [1, 1, 4, 1, 2, 1, 1, 7, 2]
def baseStart_396103 : Nat := 118140960795 + 396103 * 2 ^ 59
def prefixEnd_396103 : Nat := 4983230072969 + 3 ^ 40 * 396103 * 2
def baseEnd_396103 : Nat := 180792202389305759014099

theorem tailTrace_396103 : CollatzResearch.WordTrace tailWord_396103 prefixEnd_396103 180792202389305759014099 := by
  unfold tailWord_396103
  simp only [CollatzResearch.WordTrace]
  refine ⟨14447063283993954851696963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9631375522662636567797975 14447063283993954851696963)
  ·
    refine ⟨21670594925990932277545445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 14447063283993954851696963 21670594925990932277545445)
    ·
      refine ⟨4063236548623299802039771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 21670594925990932277545445 4063236548623299802039771)
      ·
        refine ⟨6094854822934949703059657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4063236548623299802039771 6094854822934949703059657)
        ·
          refine ⟨4571141117201212277294743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6094854822934949703059657 4571141117201212277294743)
          ·
            refine ⟨6856711675801818415942115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4571141117201212277294743 6856711675801818415942115)
            ·
              refine ⟨10285067513702727623913173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6856711675801818415942115 10285067513702727623913173)
              ·
                refine ⟨241056269852407678685465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10285067513702727623913173 241056269852407678685465)
                ·
                  refine ⟨180792202389305759014099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241056269852407678685465 180792202389305759014099)
                  ·
                    rfl

theorem cell20_396103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 7, 2].length) (baseStart_396103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396103 prefixEnd_396103 := by exact prefixLift 396103
  have htrace : WordTrace (prefixWord ++ tailWord_396103) baseStart_396103 baseEnd_396103 := by
    simpa [prefixWord, tailWord_396103, baseEnd_396103] using wordTrace_append hprefix tailTrace_396103
  have hstable : (prefixWord ++ tailWord_396103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396103).length < 2 ^ (prefixWord ++ tailWord_396103).sum := by decide
  have hdescent : baseEnd_396103 < baseStart_396103 := by decide
  rcases family_descends (prefixWord ++ tailWord_396103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396116 : List Nat := [2, 4, 1, 1, 4, 2, 2, 2, 2]
def baseStart_396116 : Nat := 118140960795 + 396116 * 2 ^ 59
def prefixEnd_396116 : Nat := 4983230072969 + 3 ^ 40 * 396116 * 2
def baseEnd_396116 : Nat := 180798135943535491580713

theorem tailTrace_396116 : CollatzResearch.WordTrace tailWord_396116 prefixEnd_396116 180798135943535491580713 := by
  unfold tailWord_396116
  simp only [CollatzResearch.WordTrace]
  refine ⟨7223768716473429035960101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9631691621964572047946801 7223768716473429035960101)
  ·
    refine ⟨1354456634338767944242519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7223768716473429035960101 1354456634338767944242519)
    ·
      refine ⟨2031684951508151916363779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1354456634338767944242519 2031684951508151916363779)
      ·
        refine ⟨3047527427262227874545669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2031684951508151916363779 3047527427262227874545669)
        ·
          refine ⟨571411392611667726477313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3047527427262227874545669 571411392611667726477313)
          ·
            refine ⟨428558544458750794857985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 571411392611667726477313 428558544458750794857985)
            ·
              refine ⟨321418908344063096143489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428558544458750794857985 321418908344063096143489)
              ·
                refine ⟨241064181258047322107617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321418908344063096143489 241064181258047322107617)
                ·
                  refine ⟨180798135943535491580713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241064181258047322107617 180798135943535491580713)
                  ·
                    rfl

theorem cell20_396116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 2, 2, 2, 2].length) (baseStart_396116 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396116 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396116 prefixEnd_396116 := by exact prefixLift 396116
  have htrace : WordTrace (prefixWord ++ tailWord_396116) baseStart_396116 baseEnd_396116 := by
    simpa [prefixWord, tailWord_396116, baseEnd_396116] using wordTrace_append hprefix tailTrace_396116
  have hstable : (prefixWord ++ tailWord_396116).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396116).length < 2 ^ (prefixWord ++ tailWord_396116).sum := by decide
  have hdescent : baseEnd_396116 < baseStart_396116 := by decide
  rcases family_descends (prefixWord ++ tailWord_396116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396169 : List Nat := [1, 2, 1, 1, 5, 3, 7]
def baseStart_396169 : Nat := 118140960795 + 396169 * 2 ^ 59
def prefixEnd_396169 : Nat := 4983230072969 + 3 ^ 40 * 396169 * 2
def baseEnd_396169 : Nat := 20091369620855873645981

theorem tailTrace_396169 : CollatzResearch.WordTrace tailWord_396169 prefixEnd_396169 20091369620855873645981 := by
  unfold tailWord_396169
  simp only [CollatzResearch.WordTrace]
  refine ⟨14449470501754848123599561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9632980334503232082399707 14449470501754848123599561)
  ·
    refine ⟨10837102876316136092699671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14449470501754848123599561 10837102876316136092699671)
    ·
      refine ⟨16255654314474204139049507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10837102876316136092699671 16255654314474204139049507)
      ·
        refine ⟨24383481471711306208574261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16255654314474204139049507 24383481471711306208574261)
        ·
          refine ⟨2285951387972934957053837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 24383481471711306208574261 2285951387972934957053837)
          ·
            refine ⟨857231770489850608895189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2285951387972934957053837 857231770489850608895189)
            ·
              refine ⟨20091369620855873645981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 857231770489850608895189 20091369620855873645981)
              ·
                rfl

theorem cell20_396169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 3, 7].length) (baseStart_396169 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396169 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396169 prefixEnd_396169 := by exact prefixLift 396169
  have htrace : WordTrace (prefixWord ++ tailWord_396169) baseStart_396169 baseEnd_396169 := by
    simpa [prefixWord, tailWord_396169, baseEnd_396169] using wordTrace_append hprefix tailTrace_396169
  have hstable : (prefixWord ++ tailWord_396169).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396169).length < 2 ^ (prefixWord ++ tailWord_396169).sum := by decide
  have hdescent : baseEnd_396169 < baseStart_396169 := by decide
  rcases family_descends (prefixWord ++ tailWord_396169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396237 : List Nat := [1, 6, 3, 1, 1, 1, 2, 5]
def baseStart_396237 : Nat := 118140960795 + 396237 * 2 ^ 59
def prefixEnd_396237 : Nat := 4983230072969 + 3 ^ 40 * 396237 * 2
def baseEnd_396237 : Nat := 60284454546865616182295

theorem tailTrace_396237 : CollatzResearch.WordTrace tailWord_396237 prefixEnd_396237 60284454546865616182295 := by
  unfold tailWord_396237
  simp only [CollatzResearch.WordTrace]
  refine ⟨14451950665508495737074965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9634633777005663824716643 14451950665508495737074965)
  ·
    refine ⟨677435187445710737675389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 14451950665508495737074965 677435187445710737675389)
    ·
      refine ⟨254038195292141526628271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 677435187445710737675389 254038195292141526628271)
      ·
        refine ⟨381057292938212289942407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 254038195292141526628271 381057292938212289942407)
        ·
          refine ⟨571585939407318434913611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 381057292938212289942407 571585939407318434913611)
          ·
            refine ⟨857378909110977652370417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571585939407318434913611 857378909110977652370417)
            ·
              refine ⟨643034181833233239277813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 857378909110977652370417 643034181833233239277813)
              ·
                refine ⟨60284454546865616182295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643034181833233239277813 60284454546865616182295)
                ·
                  rfl

theorem cell20_396237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 1, 2, 5].length) (baseStart_396237 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396237 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396237 prefixEnd_396237 := by exact prefixLift 396237
  have htrace : WordTrace (prefixWord ++ tailWord_396237) baseStart_396237 baseEnd_396237 := by
    simpa [prefixWord, tailWord_396237, baseEnd_396237] using wordTrace_append hprefix tailTrace_396237
  have hstable : (prefixWord ++ tailWord_396237).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396237).length < 2 ^ (prefixWord ++ tailWord_396237).sum := by decide
  have hdescent : baseEnd_396237 < baseStart_396237 := by decide
  rcases family_descends (prefixWord ++ tailWord_396237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396248 : List Nat := [2, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_396248 : Nat := 118140960795 + 396248 * 2 ^ 59
def prefixEnd_396248 : Nat := 4983230072969 + 3 ^ 40 * 396248 * 2
def baseEnd_396248 : Nat := 180858384340329699180173

theorem tailTrace_396248 : CollatzResearch.WordTrace tailWord_396248 prefixEnd_396248 180858384340329699180173 := by
  unfold tailWord_396248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7226175934234322307862699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9634901245645763077150265 7226175934234322307862699)
  ·
    refine ⟨10839263901351483461794049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7226175934234322307862699 10839263901351483461794049)
    ·
      refine ⟨8129447926013612596345537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10839263901351483461794049 8129447926013612596345537)
      ·
        refine ⟨6097085944510209447259153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8129447926013612596345537 6097085944510209447259153)
        ·
          refine ⟨4572814458382657085444365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6097085944510209447259153 4572814458382657085444365)
          ·
            refine ⟨1714805421893496407041637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4572814458382657085444365 1714805421893496407041637)
            ·
              refine ⟨321526016605030576320307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1714805421893496407041637 321526016605030576320307)
              ·
                refine ⟨482289024907545864480461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 321526016605030576320307 482289024907545864480461)
                ·
                  refine ⟨180858384340329699180173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 482289024907545864480461 180858384340329699180173)
                  ·
                    rfl

theorem cell20_396248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_396248 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396248 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396248 prefixEnd_396248 := by exact prefixLift 396248
  have htrace : WordTrace (prefixWord ++ tailWord_396248) baseStart_396248 baseEnd_396248 := by
    simpa [prefixWord, tailWord_396248, baseEnd_396248] using wordTrace_append hprefix tailTrace_396248
  have hstable : (prefixWord ++ tailWord_396248).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396248).length < 2 ^ (prefixWord ++ tailWord_396248).sum := by decide
  have hdescent : baseEnd_396248 < baseStart_396248 := by decide
  rcases family_descends (prefixWord ++ tailWord_396248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396289 : List Nat := [1, 2, 4, 1, 2, 4, 2, 2, 2]
def baseStart_396289 : Nat := 118140960795 + 396289 * 2 ^ 59
def prefixEnd_396289 : Nat := 4983230072969 + 3 ^ 40 * 396289 * 2
def baseEnd_396289 : Nat := 180877097857515778813339

theorem tailTrace_396289 : CollatzResearch.WordTrace tailWord_396289 prefixEnd_396289 180877097857515778813339 := by
  unfold tailWord_396289
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453847261320108617967921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9635898174213405745311947 14453847261320108617967921)
  ·
    refine ⟨10840385445990081463475941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14453847261320108617967921 10840385445990081463475941)
    ·
      refine ⟨2032572271123140274401739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10840385445990081463475941 2032572271123140274401739)
      ·
        refine ⟨3048858406684710411602609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2032572271123140274401739 3048858406684710411602609)
        ·
          refine ⟨2286643805013532808701957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3048858406684710411602609 2286643805013532808701957)
          ·
            refine ⟨428745713440037401631617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2286643805013532808701957 428745713440037401631617)
            ·
              refine ⟨321559285080028051223713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 428745713440037401631617 321559285080028051223713)
              ·
                refine ⟨241169463810021038417785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 321559285080028051223713 241169463810021038417785)
                ·
                  refine ⟨180877097857515778813339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241169463810021038417785 180877097857515778813339)
                  ·
                    rfl

theorem cell20_396289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 4, 2, 2, 2].length) (baseStart_396289 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396289 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396289 prefixEnd_396289 := by exact prefixLift 396289
  have htrace : WordTrace (prefixWord ++ tailWord_396289) baseStart_396289 baseEnd_396289 := by
    simpa [prefixWord, tailWord_396289, baseEnd_396289] using wordTrace_append hprefix tailTrace_396289
  have hstable : (prefixWord ++ tailWord_396289).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396289).length < 2 ^ (prefixWord ++ tailWord_396289).sum := by decide
  have hdescent : baseEnd_396289 < baseStart_396289 := by decide
  rcases family_descends (prefixWord ++ tailWord_396289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396293 : List Nat := [1, 3, 1, 1, 2, 3, 3, 4, 2]
def baseStart_396293 : Nat := 118140960795 + 396293 * 2 ^ 59
def prefixEnd_396293 : Nat := 4983230072969 + 3 ^ 40 * 396293 * 2
def baseEnd_396293 : Nat := 180878923566509542679989

theorem tailTrace_396293 : CollatzResearch.WordTrace tailWord_396293 prefixEnd_396293 180878923566509542679989 := by
  unfold tailWord_396293
  simp only [CollatzResearch.WordTrace]
  refine ⟨14453993153305617301113533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9635995435537078200742355 14453993153305617301113533)
  ·
    refine ⟨5420247432489606487917575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 14453993153305617301113533 5420247432489606487917575)
    ·
      refine ⟨8130371148734409731876363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420247432489606487917575 8130371148734409731876363)
      ·
        refine ⟨12195556723101614597814545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8130371148734409731876363 12195556723101614597814545)
        ·
          refine ⟨9146667542326210948360909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12195556723101614597814545 9146667542326210948360909)
          ·
            refine ⟨3430000328372329105635341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9146667542326210948360909 3430000328372329105635341)
            ·
              refine ⟨1286250123139623414613253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3430000328372329105635341 1286250123139623414613253)
              ·
                refine ⟨241171898088679390239985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1286250123139623414613253 241171898088679390239985)
                ·
                  refine ⟨180878923566509542679989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 241171898088679390239985 180878923566509542679989)
                  ·
                    rfl

theorem cell20_396293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 3, 4, 2].length) (baseStart_396293 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396293 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396293 prefixEnd_396293 := by exact prefixLift 396293
  have htrace : WordTrace (prefixWord ++ tailWord_396293) baseStart_396293 baseEnd_396293 := by
    simpa [prefixWord, tailWord_396293, baseEnd_396293] using wordTrace_append hprefix tailTrace_396293
  have hstable : (prefixWord ++ tailWord_396293).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396293).length < 2 ^ (prefixWord ++ tailWord_396293).sum := by decide
  have hdescent : baseEnd_396293 < baseStart_396293 := by decide
  rcases family_descends (prefixWord ++ tailWord_396293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396297 : List Nat := [1, 2, 1, 1, 3, 1, 1, 2, 8]
def baseStart_396297 : Nat := 118140960795 + 396297 * 2 ^ 59
def prefixEnd_396297 : Nat := 4983230072969 + 3 ^ 40 * 396297 * 2
def baseEnd_396297 : Nat := 180880749275503306546639

theorem tailTrace_396297 : CollatzResearch.WordTrace tailWord_396297 prefixEnd_396297 180880749275503306546639 := by
  unfold tailWord_396297
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454139045291125984259145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636092696860750656172763 14454139045291125984259145)
  ·
    refine ⟨10840604283968344488194359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 14454139045291125984259145 10840604283968344488194359)
    ·
      refine ⟨16260906425952516732291539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10840604283968344488194359 16260906425952516732291539)
      ·
        refine ⟨24391359638928775098437309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16260906425952516732291539 24391359638928775098437309)
        ·
          refine ⟨9146759864598290661913991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 24391359638928775098437309 9146759864598290661913991)
          ·
            refine ⟨13720139796897435992870987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9146759864598290661913991 13720139796897435992870987)
            ·
              refine ⟨20580209695346153989306481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 13720139796897435992870987 20580209695346153989306481)
              ·
                refine ⟨15435157271509615491979861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 20580209695346153989306481 15435157271509615491979861)
                ·
                  refine ⟨180880749275503306546639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 15435157271509615491979861 180880749275503306546639)
                  ·
                    rfl

theorem cell20_396297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 2, 8].length) (baseStart_396297 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396297 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396297 prefixEnd_396297 := by exact prefixLift 396297
  have htrace : WordTrace (prefixWord ++ tailWord_396297) baseStart_396297 baseEnd_396297 := by
    simpa [prefixWord, tailWord_396297, baseEnd_396297] using wordTrace_append hprefix tailTrace_396297
  have hstable : (prefixWord ++ tailWord_396297).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396297).length < 2 ^ (prefixWord ++ tailWord_396297).sum := by decide
  have hdescent : baseEnd_396297 < baseStart_396297 := by decide
  rcases family_descends (prefixWord ++ tailWord_396297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396300 : List Nat := [2, 2, 1, 2, 3, 4, 1, 5]
def baseStart_396300 : Nat := 118140960795 + 396300 * 2 ^ 59
def prefixEnd_396300 : Nat := 4983230072969 + 3 ^ 40 * 396300 * 2
def baseEnd_396300 : Nat := 60294039519082876482209

theorem tailTrace_396300 : CollatzResearch.WordTrace tailWord_396300 prefixEnd_396300 60294039519082876482209 := by
  unfold tailWord_396300
  simp only [CollatzResearch.WordTrace]
  refine ⟨7227124232140128748309177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 9636165642853504997745569 7227124232140128748309177)
  ·
    refine ⟨5420343174105096561231883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7227124232140128748309177 5420343174105096561231883)
    ·
      refine ⟨8130514761157644841847825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420343174105096561231883 8130514761157644841847825)
      ·
        refine ⟨6097886070868233631385869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8130514761157644841847825 6097886070868233631385869)
        ·
          refine ⟨2286707276575587611769701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6097886070868233631385869 2286707276575587611769701)
          ·
            refine ⟨428757614357922677206819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2286707276575587611769701 428757614357922677206819)
            ·
              refine ⟨643136421536884015810229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 428757614357922677206819 643136421536884015810229)
              ·
                refine ⟨60294039519082876482209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 643136421536884015810229 60294039519082876482209)
                ·
                  rfl

theorem cell20_396300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 4, 1, 5].length) (baseStart_396300 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396300 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396300 prefixEnd_396300 := by exact prefixLift 396300
  have htrace : WordTrace (prefixWord ++ tailWord_396300) baseStart_396300 baseEnd_396300 := by
    simpa [prefixWord, tailWord_396300, baseEnd_396300] using wordTrace_append hprefix tailTrace_396300
  have hstable : (prefixWord ++ tailWord_396300).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396300).length < 2 ^ (prefixWord ++ tailWord_396300).sum := by decide
  have hdescent : baseEnd_396300 < baseStart_396300 := by decide
  rcases family_descends (prefixWord ++ tailWord_396300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396314 : List Nat := [3, 1, 1, 3, 1, 2, 3, 2, 4]
def baseStart_396314 : Nat := 118140960795 + 396314 * 2 ^ 59
def prefixEnd_396314 : Nat := 4983230072969 + 3 ^ 40 * 396314 * 2
def baseEnd_396314 : Nat := 180888508538726802979903

theorem tailTrace_396314 : CollatzResearch.WordTrace tailWord_396314 prefixEnd_396314 180888508538726802979903 := by
  unfold tailWord_396314
  simp only [CollatzResearch.WordTrace]
  refine ⟨3613689771557384471906999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 9636506057486358591751997 3613689771557384471906999)
  ·
    refine ⟨5420534657336076707860499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3613689771557384471906999 5420534657336076707860499)
    ·
      refine ⟨8130801986004115061790749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5420534657336076707860499 8130801986004115061790749)
      ·
        refine ⟨3049050744751543148171531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8130801986004115061790749 3049050744751543148171531)
        ·
          refine ⟨4573576117127314722257297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3049050744751543148171531 4573576117127314722257297)
          ·
            refine ⟨3430182087845486041692973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4573576117127314722257297 3430182087845486041692973)
            ·
              refine ⟨1286318282942057265634865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3430182087845486041692973 1286318282942057265634865)
              ·
                refine ⟨964738712206542949226149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1286318282942057265634865 964738712206542949226149)
                ·
                  refine ⟨180888508538726802979903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 964738712206542949226149 180888508538726802979903)
                  ·
                    rfl

theorem cell20_396314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_396314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396314 prefixEnd_396314 := by exact prefixLift 396314
  have htrace : WordTrace (prefixWord ++ tailWord_396314) baseStart_396314 baseEnd_396314 := by
    simpa [prefixWord, tailWord_396314, baseEnd_396314] using wordTrace_append hprefix tailTrace_396314
  have hstable : (prefixWord ++ tailWord_396314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396314).length < 2 ^ (prefixWord ++ tailWord_396314).sum := by decide
  have hdescent : baseEnd_396314 < baseStart_396314 := by decide
  rcases family_descends (prefixWord ++ tailWord_396314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_396317 : List Nat := [1, 4, 2, 2, 3, 1, 3, 4]
def baseStart_396317 : Nat := 118140960795 + 396317 * 2 ^ 59
def prefixEnd_396317 : Nat := 4983230072969 + 3 ^ 40 * 396317 * 2
def baseEnd_396317 : Nat := 60296625940157375293297

theorem tailTrace_396317 : CollatzResearch.WordTrace tailWord_396317 prefixEnd_396317 60296625940157375293297 := by
  unfold tailWord_396317
  simp only [CollatzResearch.WordTrace]
  refine ⟨14454868505218669399987205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 9636579003479112933324803 14454868505218669399987205)
  ·
    refine ⟨2710287844728500512497601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 14454868505218669399987205 2710287844728500512497601)
    ·
      refine ⟨2032715883546375384373201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2710287844728500512497601 2032715883546375384373201)
      ·
        refine ⟨1524536912659781538279901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2032715883546375384373201 1524536912659781538279901)
        ·
          refine ⟨571701342247418076854963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1524536912659781538279901 571701342247418076854963)
          ·
            refine ⟨857552013371127115282445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 571701342247418076854963 857552013371127115282445)
            ·
              refine ⟨321582005014172668230917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 857552013371127115282445 321582005014172668230917)
              ·
                refine ⟨60296625940157375293297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 321582005014172668230917 60296625940157375293297)
                ·
                  rfl

theorem cell20_396317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 1, 3, 4].length) (baseStart_396317 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_396317 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_396317 prefixEnd_396317 := by exact prefixLift 396317
  have htrace : WordTrace (prefixWord ++ tailWord_396317) baseStart_396317 baseEnd_396317 := by
    simpa [prefixWord, tailWord_396317, baseEnd_396317] using wordTrace_append hprefix tailTrace_396317
  have hstable : (prefixWord ++ tailWord_396317).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_396317).length < 2 ^ (prefixWord ++ tailWord_396317).sum := by decide
  have hdescent : baseEnd_396317 < baseStart_396317 := by decide
  rcases family_descends (prefixWord ++ tailWord_396317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
