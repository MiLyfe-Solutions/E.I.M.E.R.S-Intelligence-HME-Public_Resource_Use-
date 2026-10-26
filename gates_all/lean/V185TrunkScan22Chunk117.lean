import V185TrunkScan22Chunk116

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_1047508 : List Nat := [2, 4, 1, 2, 1, 2, 2, 4, 4]
def baseStart_1047508 : Nat := 118140960795 + 1047508 * 2 ^ 59
def prefixEnd_1047508 : Nat := 4983230072969 + 3 ^ 40 * 1047508 * 2
def baseEnd_1047508 : Nat := 119527798539998411962801

theorem tailTrace_1047508 : CollatzResearch.WordTrace tailWord_1047508 prefixEnd_1047508 119527798539998411962801 := by
  unfold tailWord_1047508
  simp only [CollatzResearch.WordTrace]
  refine ⟨19102877744532445484271589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25470503659376593979028785 19102877744532445484271589)
  ·
    refine ⟨3581789577099833528300923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19102877744532445484271589 3581789577099833528300923)
    ·
      refine ⟨5372684365649750292451385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3581789577099833528300923 5372684365649750292451385)
      ·
        refine ⟨4029513274237312719338539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5372684365649750292451385 4029513274237312719338539)
        ·
          refine ⟨6044269911355969079007809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4029513274237312719338539 6044269911355969079007809)
          ·
            refine ⟨4533202433516976809255857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6044269911355969079007809 4533202433516976809255857)
            ·
              refine ⟨3399901825137732606941893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533202433516976809255857 3399901825137732606941893)
              ·
                refine ⟨637481592213324863801605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3399901825137732606941893 637481592213324863801605)
                ·
                  refine ⟨119527798539998411962801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637481592213324863801605 119527798539998411962801)
                  ·
                    rfl

theorem cell22_1047508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 2, 4, 4].length) (baseStart_1047508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047508 prefixEnd_1047508 := by exact prefixLift 1047508
  have htrace : WordTrace (prefixWord ++ tailWord_1047508) baseStart_1047508 baseEnd_1047508 := by
    simpa [prefixWord, tailWord_1047508, baseEnd_1047508] using wordTrace_append hprefix tailTrace_1047508
  have hstable : (prefixWord ++ tailWord_1047508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047508).length < 2 ^ (prefixWord ++ tailWord_1047508).sum := by decide
  have hdescent : baseEnd_1047508 < baseStart_1047508 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047549 : List Nat := [1, 4, 1, 1, 1, 2, 1, 2, 1, 8]
def baseStart_1047549 : Nat := 118140960795 + 1047549 * 2 ^ 59
def prefixEnd_1047549 : Nat := 4983230072969 + 3 ^ 40 * 1047549 * 2
def baseEnd_1047549 : Nat := 358597430757884795613277

theorem tailTrace_1047549 : CollatzResearch.WordTrace tailWord_1047549 prefixEnd_1047549 358597430757884795613277 := by
  unfold tailWord_1047549
  simp only [CollatzResearch.WordTrace]
  refine ⟨38207250881916354970785701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25471500587944236647190467 38207250881916354970785701)
  ·
    refine ⟨7163859540359316557022319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38207250881916354970785701 7163859540359316557022319)
    ·
      refine ⟨10745789310538974835533479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7163859540359316557022319 10745789310538974835533479)
      ·
        refine ⟨16118683965808462253300219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10745789310538974835533479 16118683965808462253300219)
        ·
          refine ⟨24178025948712693379950329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16118683965808462253300219 24178025948712693379950329)
          ·
            refine ⟨18133519461534520034962747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24178025948712693379950329 18133519461534520034962747)
            ·
              refine ⟨27200279192301780052444121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18133519461534520034962747 27200279192301780052444121)
              ·
                refine ⟨20400209394226335039333091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27200279192301780052444121 20400209394226335039333091)
                ·
                  refine ⟨30600314091339502558999637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20400209394226335039333091 30600314091339502558999637)
                  ·
                    refine ⟨358597430757884795613277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30600314091339502558999637 358597430757884795613277)
                    ·
                      rfl

theorem cell22_1047549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 8].length) (baseStart_1047549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047549 prefixEnd_1047549 := by exact prefixLift 1047549
  have htrace : WordTrace (prefixWord ++ tailWord_1047549) baseStart_1047549 baseEnd_1047549 := by
    simpa [prefixWord, tailWord_1047549, baseEnd_1047549] using wordTrace_append hprefix tailTrace_1047549
  have hstable : (prefixWord ++ tailWord_1047549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047549).length < 2 ^ (prefixWord ++ tailWord_1047549).sum := by decide
  have hdescent : baseEnd_1047549 < baseStart_1047549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047579 : List Nat := [1, 1, 1, 1, 1, 1, 3, 2, 6, 5]
def baseStart_1047579 : Nat := 118140960795 + 1047579 * 2 ^ 59
def prefixEnd_1047579 : Nat := 4983230072969 + 3 ^ 40 * 1047579 * 2
def baseEnd_1047579 : Nat := 358607700370974717363185

theorem tailTrace_1047579 : CollatzResearch.WordTrace tailWord_1047579 prefixEnd_1047579 358607700370974717363185 := by
  unfold tailWord_1047579
  simp only [CollatzResearch.WordTrace]
  refine ⟨38208345071807670094377791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25472230047871780062918527 38208345071807670094377791)
  ·
    refine ⟨57312517607711505141566687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38208345071807670094377791 57312517607711505141566687)
    ·
      refine ⟨85968776411567257712350031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57312517607711505141566687 85968776411567257712350031)
      ·
        refine ⟨128953164617350886568525047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85968776411567257712350031 128953164617350886568525047)
        ·
          refine ⟨193429746926026329852787571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128953164617350886568525047 193429746926026329852787571)
          ·
            refine ⟨290144620389039494779181357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193429746926026329852787571 290144620389039494779181357)
            ·
              refine ⟨108804232645889810542193009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290144620389039494779181357 108804232645889810542193009)
              ·
                refine ⟨81603174484417357906644757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108804232645889810542193009 81603174484417357906644757)
                ·
                  refine ⟨3825148803957063651873973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81603174484417357906644757 3825148803957063651873973)
                  ·
                    refine ⟨358607700370974717363185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825148803957063651873973 358607700370974717363185)
                    ·
                      rfl

theorem cell22_1047579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 6, 5].length) (baseStart_1047579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047579 prefixEnd_1047579 := by exact prefixLift 1047579
  have htrace : WordTrace (prefixWord ++ tailWord_1047579) baseStart_1047579 baseEnd_1047579 := by
    simpa [prefixWord, tailWord_1047579, baseEnd_1047579] using wordTrace_append hprefix tailTrace_1047579
  have hstable : (prefixWord ++ tailWord_1047579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047579).length < 2 ^ (prefixWord ++ tailWord_1047579).sum := by decide
  have hdescent : baseEnd_1047579 < baseStart_1047579 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047658 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 1, 5]
def baseStart_1047658 : Nat := 118140960795 + 1047658 * 2 ^ 59
def prefixEnd_1047658 : Nat := 4983230072969 + 3 ^ 40 * 1047658 * 2
def baseEnd_1047658 : Nat := 358634743685444844637943

theorem tailTrace_1047658 : CollatzResearch.WordTrace tailWord_1047658 prefixEnd_1047658 358634743685444844637943 := by
  unfold tailWord_1047658
  simp only [CollatzResearch.WordTrace]
  refine ⟨9552806609630366646625907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25474150959014311057669085 9552806609630366646625907)
  ·
    refine ⟨14329209914445549969938861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9552806609630366646625907 14329209914445549969938861)
    ·
      refine ⟨5373453717917081238727073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14329209914445549969938861 5373453717917081238727073)
      ·
        refine ⟨4030090288437810929045305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5373453717917081238727073 4030090288437810929045305)
        ·
          refine ⟨3022567716328358196783979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4030090288437810929045305 3022567716328358196783979)
          ·
            refine ⟨4533851574492537295175969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022567716328358196783979 4533851574492537295175969)
            ·
              refine ⟨3400388680869402971381977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4533851574492537295175969 3400388680869402971381977)
              ·
                refine ⟨2550291510652052228536483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400388680869402971381977 2550291510652052228536483)
                ·
                  refine ⟨3825437265978078342804725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550291510652052228536483 3825437265978078342804725)
                  ·
                    refine ⟨358634743685444844637943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825437265978078342804725 358634743685444844637943)
                    ·
                      rfl

theorem cell22_1047658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 5].length) (baseStart_1047658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047658 prefixEnd_1047658 := by exact prefixLift 1047658
  have htrace : WordTrace (prefixWord ++ tailWord_1047658) baseStart_1047658 baseEnd_1047658 := by
    simpa [prefixWord, tailWord_1047658, baseEnd_1047658] using wordTrace_append hprefix tailTrace_1047658
  have hstable : (prefixWord ++ tailWord_1047658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047658).length < 2 ^ (prefixWord ++ tailWord_1047658).sum := by decide
  have hdescent : baseEnd_1047658 < baseStart_1047658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047662 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 1, 4]
def baseStart_1047662 : Nat := 118140960795 + 1047662 * 2 ^ 59
def prefixEnd_1047662 : Nat := 4983230072969 + 3 ^ 40 * 1047662 * 2
def baseEnd_1047662 : Nat := 358636112967190167537931

theorem tailTrace_1047662 : CollatzResearch.WordTrace tailWord_1047662 prefixEnd_1047662 358636112967190167537931 := by
  unfold tailWord_1047662
  simp only [CollatzResearch.WordTrace]
  refine ⟨4776421541313371908706155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25474248220337983513099493 4776421541313371908706155)
  ·
    refine ⟨7164632311970057863059233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4776421541313371908706155 7164632311970057863059233)
    ·
      refine ⟨5373474233977543397294425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7164632311970057863059233 5373474233977543397294425)
      ·
        refine ⟨4030105675483157547970819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5373474233977543397294425 4030105675483157547970819)
        ·
          refine ⟨6045158513224736321956229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030105675483157547970819 6045158513224736321956229)
          ·
            refine ⟨1133467221229638060366793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6045158513224736321956229 1133467221229638060366793)
            ·
              refine ⟨850100415922228545275095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1133467221229638060366793 850100415922228545275095)
              ·
                refine ⟨1275150623883342817912643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850100415922228545275095 1275150623883342817912643)
                ·
                  refine ⟨1912725935825014226868965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275150623883342817912643 1912725935825014226868965)
                  ·
                    refine ⟨358636112967190167537931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1912725935825014226868965 358636112967190167537931)
                    ·
                      rfl

theorem cell22_1047662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 4].length) (baseStart_1047662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047662 prefixEnd_1047662 := by exact prefixLift 1047662
  have htrace : WordTrace (prefixWord ++ tailWord_1047662) baseStart_1047662 baseEnd_1047662 := by
    simpa [prefixWord, tailWord_1047662, baseEnd_1047662] using wordTrace_append hprefix tailTrace_1047662
  have hstable : (prefixWord ++ tailWord_1047662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047662).length < 2 ^ (prefixWord ++ tailWord_1047662).sum := by decide
  have hdescent : baseEnd_1047662 < baseStart_1047662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047731 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 4, 5]
def baseStart_1047731 : Nat := 118140960795 + 1047731 * 2 ^ 59
def prefixEnd_1047731 : Nat := 4983230072969 + 3 ^ 40 * 1047731 * 2
def baseEnd_1047731 : Nat := 358659733077296987562719

theorem tailTrace_1047731 : CollatzResearch.WordTrace tailWord_1047731 prefixEnd_1047731 358659733077296987562719 := by
  unfold tailWord_1047731
  simp only [CollatzResearch.WordTrace]
  refine ⟨38213888967257000053911047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25475925978171333369274031 38213888967257000053911047)
  ·
    refine ⟨57320833450885500080866571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38213888967257000053911047 57320833450885500080866571)
    ·
      refine ⟨85981250176328250121299857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57320833450885500080866571 85981250176328250121299857)
      ·
        refine ⟨64485937632246187590974893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85981250176328250121299857 64485937632246187590974893)
        ·
          refine ⟨24182226612092320346615585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64485937632246187590974893 24182226612092320346615585)
          ·
            refine ⟨18136669959069240259961689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24182226612092320346615585 18136669959069240259961689)
            ·
              refine ⟨13602502469301930194971267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18136669959069240259961689 13602502469301930194971267)
              ·
                refine ⟨20403753703952895292456901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13602502469301930194971267 20403753703952895292456901)
                ·
                  refine ⟨3825703819491167867335669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20403753703952895292456901 3825703819491167867335669)
                  ·
                    refine ⟨358659733077296987562719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3825703819491167867335669 358659733077296987562719)
                    ·
                      rfl

theorem cell22_1047731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 5].length) (baseStart_1047731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047731 prefixEnd_1047731 := by exact prefixLift 1047731
  have htrace : WordTrace (prefixWord ++ tailWord_1047731) baseStart_1047731 baseEnd_1047731 := by
    simpa [prefixWord, tailWord_1047731, baseEnd_1047731] using wordTrace_append hprefix tailTrace_1047731
  have hstable : (prefixWord ++ tailWord_1047731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047731).length < 2 ^ (prefixWord ++ tailWord_1047731).sum := by decide
  have hdescent : baseEnd_1047731 < baseStart_1047731 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047761 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 8]
def baseStart_1047761 : Nat := 118140960795 + 1047761 * 2 ^ 59
def prefixEnd_1047761 : Nat := 4983230072969 + 3 ^ 40 * 1047761 * 2
def baseEnd_1047761 : Nat := 119556667563462303104209

theorem tailTrace_1047761 : CollatzResearch.WordTrace tailWord_1047761 prefixEnd_1047761 119556667563462303104209 := by
  unfold tailWord_1047761
  simp only [CollatzResearch.WordTrace]
  refine ⟨38214983157148315177503137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25476655438098876785002091 38214983157148315177503137)
  ·
    refine ⟨28661237367861236383127353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38214983157148315177503137 28661237367861236383127353)
    ·
      refine ⟨21495928025895927287345515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28661237367861236383127353 21495928025895927287345515)
      ·
        refine ⟨32243892038843890931018273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21495928025895927287345515 32243892038843890931018273)
        ·
          refine ⟨24182919029132918198263705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32243892038843890931018273 24182919029132918198263705)
          ·
            refine ⟨18137189271849688648697779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24182919029132918198263705 18137189271849688648697779)
            ·
              refine ⟨27205783907774532973046669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18137189271849688648697779 27205783907774532973046669)
              ·
                refine ⟨10202168965415449864892501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27205783907774532973046669 10202168965415449864892501)
                ·
                  refine ⟨119556667563462303104209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10202168965415449864892501 119556667563462303104209)
                  ·
                    rfl

theorem cell22_1047761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 8].length) (baseStart_1047761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047761 prefixEnd_1047761 := by exact prefixLift 1047761
  have htrace : WordTrace (prefixWord ++ tailWord_1047761) baseStart_1047761 baseEnd_1047761 := by
    simpa [prefixWord, tailWord_1047761, baseEnd_1047761] using wordTrace_append hprefix tailTrace_1047761
  have hstable : (prefixWord ++ tailWord_1047761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047761).length < 2 ^ (prefixWord ++ tailWord_1047761).sum := by decide
  have hdescent : baseEnd_1047761 < baseStart_1047761 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047795 : List Nat := [1, 1, 1, 2, 2, 6, 1, 4, 4]
def baseStart_1047795 : Nat := 118140960795 + 1047795 * 2 ^ 59
def prefixEnd_1047795 : Nat := 4983230072969 + 3 ^ 40 * 1047795 * 2
def baseEnd_1047795 : Nat := 119560547195074051320841

theorem tailTrace_1047795 : CollatzResearch.WordTrace tailWord_1047795 prefixEnd_1047795 119560547195074051320841 := by
  unfold tailWord_1047795
  simp only [CollatzResearch.WordTrace]
  refine ⟨38216223239025138984240839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25477482159350092656160559 38216223239025138984240839)
  ·
    refine ⟨57324334858537708476361259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38216223239025138984240839 57324334858537708476361259)
    ·
      refine ⟨85986502287806562714541889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57324334858537708476361259 85986502287806562714541889)
      ·
        refine ⟨64489876715854922035906417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85986502287806562714541889 64489876715854922035906417)
        ·
          refine ⟨48367407536891191526929813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64489876715854922035906417 48367407536891191526929813)
          ·
            refine ⟨2267222228291774602824835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48367407536891191526929813 2267222228291774602824835)
            ·
              refine ⟨3400833342437661904237253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2267222228291774602824835 3400833342437661904237253)
              ·
                refine ⟨637656251707061607044485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3400833342437661904237253 637656251707061607044485)
                ·
                  refine ⟨119560547195074051320841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 637656251707061607044485 119560547195074051320841)
                  ·
                    rfl

theorem cell22_1047795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 6, 1, 4, 4].length) (baseStart_1047795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047795 prefixEnd_1047795 := by exact prefixLift 1047795
  have htrace : WordTrace (prefixWord ++ tailWord_1047795) baseStart_1047795 baseEnd_1047795 := by
    simpa [prefixWord, tailWord_1047795, baseEnd_1047795] using wordTrace_append hprefix tailTrace_1047795
  have hstable : (prefixWord ++ tailWord_1047795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047795).length < 2 ^ (prefixWord ++ tailWord_1047795).sum := by decide
  have hdescent : baseEnd_1047795 < baseStart_1047795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047906 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 1, 3]
def baseStart_1047906 : Nat := 118140960795 + 1047906 * 2 ^ 59
def prefixEnd_1047906 : Nat := 4983230072969 + 3 ^ 40 * 1047906 * 2
def baseEnd_1047906 : Nat := 358719639153654864437183

theorem tailTrace_1047906 : CollatzResearch.WordTrace tailWord_1047906 prefixEnd_1047906 358719639153654864437183 := by
  unfold tailWord_1047906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555067935405751235382893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25480181161082003294354381 9555067935405751235382893)
  ·
    refine ⟨3583150475777156713268585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9555067935405751235382893 3583150475777156713268585)
    ·
      refine ⟨2687362856832867534951439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3583150475777156713268585 2687362856832867534951439)
      ·
        refine ⟨4031044285249301302427159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687362856832867534951439 4031044285249301302427159)
        ·
          refine ⟨6046566427873951953640739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031044285249301302427159 6046566427873951953640739)
          ·
            refine ⟨9069849641810927930461109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046566427873951953640739 9069849641810927930461109)
            ·
              refine ⟨850298403919774493480729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9069849641810927930461109 850298403919774493480729)
              ·
                refine ⟨637723802939830870110547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850298403919774493480729 637723802939830870110547)
                ·
                  refine ⟨956585704409746305165821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637723802939830870110547 956585704409746305165821)
                  ·
                    refine ⟨358719639153654864437183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956585704409746305165821 358719639153654864437183)
                    ·
                      rfl

theorem cell22_1047906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_1047906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047906 prefixEnd_1047906 := by exact prefixLift 1047906
  have htrace : WordTrace (prefixWord ++ tailWord_1047906) baseStart_1047906 baseEnd_1047906 := by
    simpa [prefixWord, tailWord_1047906, baseEnd_1047906] using wordTrace_append hprefix tailTrace_1047906
  have hstable : (prefixWord ++ tailWord_1047906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047906).length < 2 ^ (prefixWord ++ tailWord_1047906).sum := by decide
  have hdescent : baseEnd_1047906 < baseStart_1047906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047913 : List Nat := [1, 2, 1, 1, 1, 3, 2, 5, 6]
def baseStart_1047913 : Nat := 118140960795 + 1047913 * 2 ^ 59
def prefixEnd_1047913 : Nat := 4983230072969 + 3 ^ 40 * 1047913 * 2
def baseEnd_1047913 : Nat := 119574011798903059837387

theorem tailTrace_1047913 : CollatzResearch.WordTrace tailWord_1047913 prefixEnd_1047913 119574011798903059837387 := by
  unfold tailWord_1047913
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220527052597645137036393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25480351368398430091357595 38220527052597645137036393)
  ·
    refine ⟨28665395289448233852777295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38220527052597645137036393 28665395289448233852777295)
    ·
      refine ⟨42998092934172350779165943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28665395289448233852777295 42998092934172350779165943)
      ·
        refine ⟨64497139401258526168748915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42998092934172350779165943 64497139401258526168748915)
        ·
          refine ⟨96745709101887789253123373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64497139401258526168748915 96745709101887789253123373)
          ·
            refine ⟨36279640913207920969921265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96745709101887789253123373 36279640913207920969921265)
            ·
              refine ⟨27209730684905940727440949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36279640913207920969921265 27209730684905940727440949)
              ·
                refine ⟨2550912251709931943197589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27209730684905940727440949 2550912251709931943197589)
                ·
                  refine ⟨119574011798903059837387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2550912251709931943197589 119574011798903059837387)
                  ·
                    rfl

theorem cell22_1047913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 5, 6].length) (baseStart_1047913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047913 prefixEnd_1047913 := by exact prefixLift 1047913
  have htrace : WordTrace (prefixWord ++ tailWord_1047913) baseStart_1047913 baseEnd_1047913 := by
    simpa [prefixWord, tailWord_1047913, baseEnd_1047913] using wordTrace_append hprefix tailTrace_1047913
  have hstable : (prefixWord ++ tailWord_1047913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047913).length < 2 ^ (prefixWord ++ tailWord_1047913).sum := by decide
  have hdescent : baseEnd_1047913 < baseStart_1047913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1047928 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 7, 5]
def baseStart_1047928 : Nat := 118140960795 + 1047928 * 2 ^ 59
def prefixEnd_1047928 : Nat := 4983230072969 + 3 ^ 40 * 1047928 * 2
def baseEnd_1047928 : Nat := 358727170203254140387115

theorem tailTrace_1047928 : CollatzResearch.WordTrace tailWord_1047928 prefixEnd_1047928 358727170203254140387115 := by
  unfold tailWord_1047928
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110537073771651349416219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25480716098362201799221625 19110537073771651349416219)
  ·
    refine ⟨28665805610657477024124329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19110537073771651349416219 28665805610657477024124329)
    ·
      refine ⟨21499354207993107768093247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28665805610657477024124329 21499354207993107768093247)
      ·
        refine ⟨32249031311989661652139871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21499354207993107768093247 32249031311989661652139871)
        ·
          refine ⟨48373546967984492478209807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32249031311989661652139871 48373546967984492478209807)
          ·
            refine ⟨72560320451976738717314711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48373546967984492478209807 72560320451976738717314711)
            ·
              refine ⟨108840480677965108075972067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72560320451976738717314711 108840480677965108075972067)
              ·
                refine ⟨163260721016947662113958101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108840480677965108075972067 163260721016947662113958101)
                ·
                  refine ⟨3826423148834710830795893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 163260721016947662113958101 3826423148834710830795893)
                  ·
                    refine ⟨358727170203254140387115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3826423148834710830795893 358727170203254140387115)
                    ·
                      rfl

theorem cell22_1047928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 5].length) (baseStart_1047928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1047928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1047928 prefixEnd_1047928 := by exact prefixLift 1047928
  have htrace : WordTrace (prefixWord ++ tailWord_1047928) baseStart_1047928 baseEnd_1047928 := by
    simpa [prefixWord, tailWord_1047928, baseEnd_1047928] using wordTrace_append hprefix tailTrace_1047928
  have hstable : (prefixWord ++ tailWord_1047928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1047928).length < 2 ^ (prefixWord ++ tailWord_1047928).sum := by decide
  have hdescent : baseEnd_1047928 < baseStart_1047928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1047928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048024 : List Nat := [2, 1, 2, 2, 2, 1, 4, 4, 1, 3]
def baseStart_1048024 : Nat := 118140960795 + 1048024 * 2 ^ 59
def prefixEnd_1048024 : Nat := 4983230072969 + 3 ^ 40 * 1048024 * 2
def baseEnd_1048024 : Nat := 358760032965141889986821

theorem tailTrace_1048024 : CollatzResearch.WordTrace tailWord_1048024 prefixEnd_1048024 358760032965141889986821 := by
  unfold tailWord_1048024
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112287777597755547163563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25483050370130340729551417 19112287777597755547163563)
  ·
    refine ⟨28668431666396633320745345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19112287777597755547163563 28668431666396633320745345)
    ·
      refine ⟨21501323749797474990559009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28668431666396633320745345 21501323749797474990559009)
      ·
        refine ⟨16125992812348106242919257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21501323749797474990559009 16125992812348106242919257)
        ·
          refine ⟨12094494609261079682189443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16125992812348106242919257 12094494609261079682189443)
          ·
            refine ⟨18141741913891619523284165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094494609261079682189443 18141741913891619523284165)
            ·
              refine ⟨3401576608854678660615781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18141741913891619523284165 3401576608854678660615781)
              ·
                refine ⟨637795614160252248865459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3401576608854678660615781 637795614160252248865459)
                ·
                  refine ⟨956693421240378373298189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637795614160252248865459 956693421240378373298189)
                  ·
                    refine ⟨358760032965141889986821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956693421240378373298189 358760032965141889986821)
                    ·
                      rfl

theorem cell22_1048024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 4, 1, 3].length) (baseStart_1048024 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048024 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048024 prefixEnd_1048024 := by exact prefixLift 1048024
  have htrace : WordTrace (prefixWord ++ tailWord_1048024) baseStart_1048024 baseEnd_1048024 := by
    simpa [prefixWord, tailWord_1048024, baseEnd_1048024] using wordTrace_append hprefix tailTrace_1048024
  have hstable : (prefixWord ++ tailWord_1048024).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048024).length < 2 ^ (prefixWord ++ tailWord_1048024).sum := by decide
  have hdescent : baseEnd_1048024 < baseStart_1048024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048095 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 6]
def baseStart_1048095 : Nat := 118140960795 + 1048095 * 2 ^ 59
def prefixEnd_1048095 : Nat := 4983230072969 + 3 ^ 40 * 1048095 * 2
def baseEnd_1048095 : Nat := 358784337716121371461603

theorem tailTrace_1048095 : CollatzResearch.WordTrace tailWord_1048095 prefixEnd_1048095 358784337716121371461603 := by
  unfold tailWord_1048095
  simp only [CollatzResearch.WordTrace]
  refine ⟨38227165137938290220161739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25484776758625526813441159 38227165137938290220161739)
  ·
    refine ⟨57340747706907435330242609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38227165137938290220161739 57340747706907435330242609)
    ·
      refine ⟨43005560780180576497681957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57340747706907435330242609 43005560780180576497681957)
      ·
        refine ⟨8063542646283858093315367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43005560780180576497681957 8063542646283858093315367)
        ·
          refine ⟨12095313969425787139973051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063542646283858093315367 12095313969425787139973051)
          ·
            refine ⟨18142970954138680709959577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095313969425787139973051 18142970954138680709959577)
            ·
              refine ⟨13607228215604010532469683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18142970954138680709959577 13607228215604010532469683)
              ·
                refine ⟨20410842323406015798704525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607228215604010532469683 20410842323406015798704525)
                ·
                  refine ⟨7654065871277255924514197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20410842323406015798704525 7654065871277255924514197)
                  ·
                    refine ⟨358784337716121371461603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7654065871277255924514197 358784337716121371461603)
                    ·
                      rfl

theorem cell22_1048095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 6].length) (baseStart_1048095 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048095 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048095 prefixEnd_1048095 := by exact prefixLift 1048095
  have htrace : WordTrace (prefixWord ++ tailWord_1048095) baseStart_1048095 baseEnd_1048095 := by
    simpa [prefixWord, tailWord_1048095, baseEnd_1048095] using wordTrace_append hprefix tailTrace_1048095
  have hstable : (prefixWord ++ tailWord_1048095).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048095).length < 2 ^ (prefixWord ++ tailWord_1048095).sum := by decide
  have hdescent : baseEnd_1048095 < baseStart_1048095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048118 : List Nat := [5, 1, 2, 1, 3, 1, 3, 1, 1, 4]
def baseStart_1048118 : Nat := 118140960795 + 1048118 * 2 ^ 59
def prefixEnd_1048118 : Nat := 4983230072969 + 3 ^ 40 * 1048118 * 2
def baseEnd_1048118 : Nat := 358792211086156978136533

theorem tailTrace_1048118 : CollatzResearch.WordTrace tailWord_1048118 prefixEnd_1048118 358792211086156978136533 := by
  unfold tailWord_1048118
  simp only [CollatzResearch.WordTrace]
  refine ⟨2389250251053435321765563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25485336011236643432166005 2389250251053435321765563)
  ·
    refine ⟨3583875376580152982648345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2389250251053435321765563 3583875376580152982648345)
    ·
      refine ⟨2687906532435114736986259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3583875376580152982648345 2687906532435114736986259)
      ·
        refine ⟨4031859798652672105479389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687906532435114736986259 4031859798652672105479389)
        ·
          refine ⟨1511947424494752039554771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4031859798652672105479389 1511947424494752039554771)
          ·
            refine ⟨2267921136742128059332157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1511947424494752039554771 2267921136742128059332157)
            ·
              refine ⟨850470426278298022249559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2267921136742128059332157 850470426278298022249559)
              ·
                refine ⟨1275705639417447033374339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850470426278298022249559 1275705639417447033374339)
                ·
                  refine ⟨1913558459126170550061509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1275705639417447033374339 1913558459126170550061509)
                  ·
                    refine ⟨358792211086156978136533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1913558459126170550061509 358792211086156978136533)
                    ·
                      rfl

theorem cell22_1048118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_1048118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048118 prefixEnd_1048118 := by exact prefixLift 1048118
  have htrace : WordTrace (prefixWord ++ tailWord_1048118) baseStart_1048118 baseEnd_1048118 := by
    simpa [prefixWord, tailWord_1048118, baseEnd_1048118] using wordTrace_append hprefix tailTrace_1048118
  have hstable : (prefixWord ++ tailWord_1048118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048118).length < 2 ^ (prefixWord ++ tailWord_1048118).sum := by decide
  have hdescent : baseEnd_1048118 < baseStart_1048118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048176 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 1, 3]
def baseStart_1048176 : Nat := 118140960795 + 1048176 * 2 ^ 59
def prefixEnd_1048176 : Nat := 4983230072969 + 3 ^ 40 * 1048176 * 2
def baseEnd_1048176 : Nat := 358812065671464160186355

theorem tailTrace_1048176 : CollatzResearch.WordTrace tailWord_1048176 prefixEnd_1048176 358812065671464160186355 := by
  unfold tailWord_1048176
  simp only [CollatzResearch.WordTrace]
  refine ⟨19115059725322420526930191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25486746300429894035906921 19115059725322420526930191)
  ·
    refine ⟨28672589587983630790395287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19115059725322420526930191 28672589587983630790395287)
    ·
      refine ⟨43008884381975446185592931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28672589587983630790395287 43008884381975446185592931)
      ·
        refine ⟨64513326572963169278389397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43008884381975446185592931 64513326572963169278389397)
        ·
          refine ⟨3024062183107648559924503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 64513326572963169278389397 3024062183107648559924503)
          ·
            refine ⟨4536093274661472839886755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024062183107648559924503 4536093274661472839886755)
            ·
              refine ⟨6804139911992209259830133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536093274661472839886755 6804139911992209259830133)
              ·
                refine ⟨637888116749269618109075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6804139911992209259830133 637888116749269618109075)
                ·
                  refine ⟨956832175123904427163613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 637888116749269618109075 956832175123904427163613)
                  ·
                    refine ⟨358812065671464160186355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956832175123904427163613 358812065671464160186355)
                    ·
                      rfl

theorem cell22_1048176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 3].length) (baseStart_1048176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048176 prefixEnd_1048176 := by exact prefixLift 1048176
  have htrace : WordTrace (prefixWord ++ tailWord_1048176) baseStart_1048176 baseEnd_1048176 := by
    simpa [prefixWord, tailWord_1048176, baseEnd_1048176] using wordTrace_append hprefix tailTrace_1048176
  have hstable : (prefixWord ++ tailWord_1048176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048176).length < 2 ^ (prefixWord ++ tailWord_1048176).sum := by decide
  have hdescent : baseEnd_1048176 < baseStart_1048176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048189 : List Nat := [1, 4, 1, 1, 4, 1, 3, 2, 5]
def baseStart_1048189 : Nat := 118140960795 + 1048189 * 2 ^ 59
def prefixEnd_1048189 : Nat := 4983230072969 + 3 ^ 40 * 1048189 * 2
def baseEnd_1048189 : Nat := 119605505279045486537105

theorem tailTrace_1048189 : CollatzResearch.WordTrace tailWord_1048189 prefixEnd_1048189 119605505279045486537105 := by
  unfold tailWord_1048189
  simp only [CollatzResearch.WordTrace]
  refine ⟨38230593599597744274083621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25487062399731829516055747 38230593599597744274083621)
  ·
    refine ⟨7168236299924577051390679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38230593599597744274083621 7168236299924577051390679)
    ·
      refine ⟨10752354449886865577086019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168236299924577051390679 10752354449886865577086019)
      ·
        refine ⟨16128531674830298365629029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10752354449886865577086019 16128531674830298365629029)
        ·
          refine ⟨3024099689030680943555443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16128531674830298365629029 3024099689030680943555443)
          ·
            refine ⟨4536149533546021415333165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024099689030680943555443 4536149533546021415333165)
            ·
              refine ⟨1701056075079758030749937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4536149533546021415333165 1701056075079758030749937)
              ·
                refine ⟨1275792056309818523062453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701056075079758030749937 1275792056309818523062453)
                ·
                  refine ⟨119605505279045486537105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1275792056309818523062453 119605505279045486537105)
                  ·
                    rfl

theorem cell22_1048189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 2, 5].length) (baseStart_1048189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048189 prefixEnd_1048189 := by exact prefixLift 1048189
  have htrace : WordTrace (prefixWord ++ tailWord_1048189) baseStart_1048189 baseEnd_1048189 := by
    simpa [prefixWord, tailWord_1048189, baseEnd_1048189] using wordTrace_append hprefix tailTrace_1048189
  have hstable : (prefixWord ++ tailWord_1048189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048189).length < 2 ^ (prefixWord ++ tailWord_1048189).sum := by decide
  have hdescent : baseEnd_1048189 < baseStart_1048189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048206 : List Nat := [4, 1, 1, 3, 1, 3, 3, 1, 5]
def baseStart_1048206 : Nat := 118140960795 + 1048206 * 2 ^ 59
def prefixEnd_1048206 : Nat := 4983230072969 + 3 ^ 40 * 1048206 * 2
def baseEnd_1048206 : Nat := 119607445094851360645421

theorem tailTrace_1048206 : CollatzResearch.WordTrace tailWord_1048206 prefixEnd_1048206 119607445094851360645421 := by
  unfold tailWord_1048206
  simp only [CollatzResearch.WordTrace]
  refine ⟨4778901705067019522181559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25487475760357437451634981 4778901705067019522181559)
  ·
    refine ⟨7168352557600529283272339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4778901705067019522181559 7168352557600529283272339)
    ·
      refine ⟨10752528836400793924908509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168352557600529283272339 10752528836400793924908509)
      ·
        refine ⟨4032198313650297721840691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10752528836400793924908509 4032198313650297721840691)
        ·
          refine ⟨6048297470475446582761037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032198313650297721840691 6048297470475446582761037)
          ·
            refine ⟨2268111551428292468535389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6048297470475446582761037 2268111551428292468535389)
            ·
              refine ⟨850541831785609675700771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2268111551428292468535389 850541831785609675700771)
              ·
                refine ⟨1275812747678414513551157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 850541831785609675700771 1275812747678414513551157)
                ·
                  refine ⟨119607445094851360645421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1275812747678414513551157 119607445094851360645421)
                  ·
                    rfl

theorem cell22_1048206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 5].length) (baseStart_1048206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048206 prefixEnd_1048206 := by exact prefixLift 1048206
  have htrace : WordTrace (prefixWord ++ tailWord_1048206) baseStart_1048206 baseEnd_1048206 := by
    simpa [prefixWord, tailWord_1048206, baseEnd_1048206] using wordTrace_append hprefix tailTrace_1048206
  have hstable : (prefixWord ++ tailWord_1048206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048206).length < 2 ^ (prefixWord ++ tailWord_1048206).sum := by decide
  have hdescent : baseEnd_1048206 < baseStart_1048206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048249 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 4, 3]
def baseStart_1048249 : Nat := 118140960795 + 1048249 * 2 ^ 59
def prefixEnd_1048249 : Nat := 4983230072969 + 3 ^ 40 * 1048249 * 2
def baseEnd_1048249 : Nat := 358837055063316303111131

theorem tailTrace_1048249 : CollatzResearch.WordTrace tailWord_1048249 prefixEnd_1048249 358837055063316303111131 := by
  unfold tailWord_1048249
  simp only [CollatzResearch.WordTrace]
  refine ⟨38232781979380374521267801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25488521319586916347511867 38232781979380374521267801)
  ·
    refine ⟨28674586484535280890950851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38232781979380374521267801 28674586484535280890950851)
    ·
      refine ⟨43011879726802921336426277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28674586484535280890950851 43011879726802921336426277)
      ·
        refine ⟨8064727448775547750579927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43011879726802921336426277 8064727448775547750579927)
        ·
          refine ⟨12097091173163321625869891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064727448775547750579927 12097091173163321625869891)
          ·
            refine ⟨18145636759744982438804837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12097091173163321625869891 18145636759744982438804837)
            ·
              refine ⟨3402306892452184207275907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18145636759744982438804837 3402306892452184207275907)
              ·
                refine ⟨5103460338678276310913861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402306892452184207275907 5103460338678276310913861)
                ·
                  refine ⟨956898813502176808296349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5103460338678276310913861 956898813502176808296349)
                  ·
                    refine ⟨358837055063316303111131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 956898813502176808296349 358837055063316303111131)
                    ·
                      rfl

theorem cell22_1048249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 3].length) (baseStart_1048249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048249 prefixEnd_1048249 := by exact prefixLift 1048249
  have htrace : WordTrace (prefixWord ++ tailWord_1048249) baseStart_1048249 baseEnd_1048249 := by
    simpa [prefixWord, tailWord_1048249, baseEnd_1048249] using wordTrace_append hprefix tailTrace_1048249
  have hstable : (prefixWord ++ tailWord_1048249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048249).length < 2 ^ (prefixWord ++ tailWord_1048249).sum := by decide
  have hdescent : baseEnd_1048249 < baseStart_1048249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048307 : List Nat := [1, 1, 1, 2, 2, 3, 2, 3, 7]
def baseStart_1048307 : Nat := 118140960795 + 1048307 * 2 ^ 59
def prefixEnd_1048307 : Nat := 4983230072969 + 3 ^ 40 * 1048307 * 2
def baseEnd_1048307 : Nat := 119618969882874495053651

theorem tailTrace_1048307 : CollatzResearch.WordTrace tailWord_1048307 prefixEnd_1048307 119618969882874495053651 := by
  unfold tailWord_1048307
  simp only [CollatzResearch.WordTrace]
  refine ⟨38234897413170250426879175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25489931608780166951252783 38234897413170250426879175)
  ·
    refine ⟨57352346119755375640318763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38234897413170250426879175 57352346119755375640318763)
    ·
      refine ⟨86028519179633063460478145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57352346119755375640318763 86028519179633063460478145)
      ·
        refine ⟨64521389384724797595358609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86028519179633063460478145 64521389384724797595358609)
        ·
          refine ⟨48391042038543598196518957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64521389384724797595358609 48391042038543598196518957)
          ·
            refine ⟨18146640764453849323694609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48391042038543598196518957 18146640764453849323694609)
            ·
              refine ⟨13609980573340386992770957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18146640764453849323694609 13609980573340386992770957)
              ·
                refine ⟨5103742715002645122289109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13609980573340386992770957 5103742715002645122289109)
                ·
                  refine ⟨119618969882874495053651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5103742715002645122289109 119618969882874495053651)
                  ·
                    rfl

theorem cell22_1048307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 3, 7].length) (baseStart_1048307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048307 prefixEnd_1048307 := by exact prefixLift 1048307
  have htrace : WordTrace (prefixWord ++ tailWord_1048307) baseStart_1048307 baseEnd_1048307 := by
    simpa [prefixWord, tailWord_1048307, baseEnd_1048307] using wordTrace_append hprefix tailTrace_1048307
  have hstable : (prefixWord ++ tailWord_1048307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048307).length < 2 ^ (prefixWord ++ tailWord_1048307).sum := by decide
  have hdescent : baseEnd_1048307 < baseStart_1048307 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048369 : List Nat := [1, 2, 2, 3, 2, 2, 1, 3, 6]
def baseStart_1048369 : Nat := 118140960795 + 1048369 * 2 ^ 59
def prefixEnd_1048369 : Nat := 4983230072969 + 3 ^ 40 * 1048369 * 2
def baseEnd_1048369 : Nat := 119626044505225330036921

theorem tailTrace_1048369 : CollatzResearch.WordTrace tailWord_1048369 prefixEnd_1048369 119626044505225330036921 := by
  unfold tailWord_1048369
  simp only [CollatzResearch.WordTrace]
  refine ⟨38237158738945635015636161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25491439159297090010424107 38237158738945635015636161)
  ·
    refine ⟨28677869054209226261727121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38237158738945635015636161 28677869054209226261727121)
    ·
      refine ⟨21508401790656919696295341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28677869054209226261727121 21508401790656919696295341)
      ·
        refine ⟨8065650671496344886110753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21508401790656919696295341 8065650671496344886110753)
        ·
          refine ⟨6049238003622258664583065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8065650671496344886110753 6049238003622258664583065)
          ·
            refine ⟨4536928502716693998437299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6049238003622258664583065 4536928502716693998437299)
            ·
              refine ⟨6805392754075040997655949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536928502716693998437299 6805392754075040997655949)
              ·
                refine ⟨2552022282778140374120981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6805392754075040997655949 2552022282778140374120981)
                ·
                  refine ⟨119626044505225330036921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2552022282778140374120981 119626044505225330036921)
                  ·
                    rfl

theorem cell22_1048369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 3, 6].length) (baseStart_1048369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048369 prefixEnd_1048369 := by exact prefixLift 1048369
  have htrace : WordTrace (prefixWord ++ tailWord_1048369) baseStart_1048369 baseEnd_1048369 := by
    simpa [prefixWord, tailWord_1048369, baseEnd_1048369] using wordTrace_append hprefix tailTrace_1048369
  have hstable : (prefixWord ++ tailWord_1048369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048369).length < 2 ^ (prefixWord ++ tailWord_1048369).sum := by decide
  have hdescent : baseEnd_1048369 < baseStart_1048369 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048401 : List Nat := [1, 2, 2, 1, 5, 1, 1, 2, 4, 3]
def baseStart_1048401 : Nat := 118140960795 + 1048401 * 2 ^ 59
def prefixEnd_1048401 : Nat := 4983230072969 + 3 ^ 40 * 1048401 * 2
def baseEnd_1048401 : Nat := 358889087769638573310665

theorem tailTrace_1048401 : CollatzResearch.WordTrace tailWord_1048401 prefixEnd_1048401 358889087769638573310665 := by
  unfold tailWord_1048401
  simp only [CollatzResearch.WordTrace]
  refine ⟨38238325874829704480801057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25492217249886469653867371 38238325874829704480801057)
  ·
    refine ⟨28678744406122278360600793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38238325874829704480801057 28678744406122278360600793)
    ·
      refine ⟨21509058304591708770450595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28678744406122278360600793 21509058304591708770450595)
      ·
        refine ⟨32263587456887563155675893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21509058304591708770450595 32263587456887563155675893)
        ·
          refine ⟨3024711324083209045844615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32263587456887563155675893 3024711324083209045844615)
          ·
            refine ⟨4537066986124813568766923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024711324083209045844615 4537066986124813568766923)
            ·
              refine ⟨6805600479187220353150385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537066986124813568766923 6805600479187220353150385)
              ·
                refine ⟨5104200359390415264862789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805600479187220353150385 5104200359390415264862789)
                ·
                  refine ⟨957037567385702862161773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5104200359390415264862789 957037567385702862161773)
                  ·
                    refine ⟨358889087769638573310665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957037567385702862161773 358889087769638573310665)
                    ·
                      rfl

theorem cell22_1048401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 2, 4, 3].length) (baseStart_1048401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048401 prefixEnd_1048401 := by exact prefixLift 1048401
  have htrace : WordTrace (prefixWord ++ tailWord_1048401) baseStart_1048401 baseEnd_1048401 := by
    simpa [prefixWord, tailWord_1048401, baseEnd_1048401] using wordTrace_append hprefix tailTrace_1048401
  have hstable : (prefixWord ++ tailWord_1048401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048401).length < 2 ^ (prefixWord ++ tailWord_1048401).sum := by decide
  have hdescent : baseEnd_1048401 < baseStart_1048401 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048416 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 2, 4]
def baseStart_1048416 : Nat := 118140960795 + 1048416 * 2 ^ 59
def prefixEnd_1048416 : Nat := 4983230072969 + 3 ^ 40 * 1048416 * 2
def baseEnd_1048416 : Nat := 358894222576183534185619

theorem tailTrace_1048416 : CollatzResearch.WordTrace tailWord_1048416 prefixEnd_1048416 358894222576183534185619 := by
  unfold tailWord_1048416
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119436484887681021298551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25492581979850241361731401 19119436484887681021298551)
  ·
    refine ⟨28679154727331521531947827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19119436484887681021298551 28679154727331521531947827)
    ·
      refine ⟨43018732090997282297921741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28679154727331521531947827 43018732090997282297921741)
      ·
        refine ⟨16132024534123980861720653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43018732090997282297921741 16132024534123980861720653)
        ·
          refine ⟨6049509200296492823145245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16132024534123980861720653 6049509200296492823145245)
          ·
            refine ⟨2268565950111184808679467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6049509200296492823145245 2268565950111184808679467)
            ·
              refine ⟨3402848925166777213019201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2268565950111184808679467 3402848925166777213019201)
              ·
                refine ⟨2552136693875082909764401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402848925166777213019201 2552136693875082909764401)
                ·
                  refine ⟨1914102520406312182323301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2552136693875082909764401 1914102520406312182323301)
                  ·
                    refine ⟨358894222576183534185619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1914102520406312182323301 358894222576183534185619)
                    ·
                      rfl

theorem cell22_1048416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 4].length) (baseStart_1048416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048416 prefixEnd_1048416 := by exact prefixLift 1048416
  have htrace : WordTrace (prefixWord ++ tailWord_1048416) baseStart_1048416 baseEnd_1048416 := by
    simpa [prefixWord, tailWord_1048416, baseEnd_1048416] using wordTrace_append hprefix tailTrace_1048416
  have hstable : (prefixWord ++ tailWord_1048416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048416).length < 2 ^ (prefixWord ++ tailWord_1048416).sum := by decide
  have hdescent : baseEnd_1048416 < baseStart_1048416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048418 : List Nat := [3, 3, 2, 1, 2, 1, 2, 1, 4, 3]
def baseStart_1048418 : Nat := 118140960795 + 1048418 * 2 ^ 59
def prefixEnd_1048418 : Nat := 4983230072969 + 3 ^ 40 * 1048418 * 2
def baseEnd_1048418 : Nat := 358894907217056195635613

theorem tailTrace_1048418 : CollatzResearch.WordTrace tailWord_1048418 prefixEnd_1048418 358894907217056195635613 := by
  unfold tailWord_1048418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9559736478942029096042477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25492630610512077589446605 9559736478942029096042477)
  ·
    refine ⟨3584901179603260911015929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9559736478942029096042477 3584901179603260911015929)
    ·
      refine ⟨2688675884702445683261947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3584901179603260911015929 2688675884702445683261947)
      ·
        refine ⟨4033013827053668524892921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688675884702445683261947 4033013827053668524892921)
        ·
          refine ⟨3024760370290251393669691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4033013827053668524892921 3024760370290251393669691)
          ·
            refine ⟨4537140555435377090504537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024760370290251393669691 4537140555435377090504537)
            ·
              refine ⟨3402855416576532817878403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4537140555435377090504537 3402855416576532817878403)
              ·
                refine ⟨5104283124864799226817605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402855416576532817878403 5104283124864799226817605)
                ·
                  refine ⟨957053085912149855028301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5104283124864799226817605 957053085912149855028301)
                  ·
                    refine ⟨358894907217056195635613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957053085912149855028301 358894907217056195635613)
                    ·
                      rfl

theorem cell22_1048418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_1048418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048418 prefixEnd_1048418 := by exact prefixLift 1048418
  have htrace : WordTrace (prefixWord ++ tailWord_1048418) baseStart_1048418 baseEnd_1048418 := by
    simpa [prefixWord, tailWord_1048418, baseEnd_1048418] using wordTrace_append hprefix tailTrace_1048418
  have hstable : (prefixWord ++ tailWord_1048418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048418).length < 2 ^ (prefixWord ++ tailWord_1048418).sum := by decide
  have hdescent : baseEnd_1048418 < baseStart_1048418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048420 : List Nat := [2, 3, 1, 1, 5, 1, 3, 2, 4]
def baseStart_1048420 : Nat := 118140960795 + 1048420 * 2 ^ 59
def prefixEnd_1048420 : Nat := 4983230072969 + 3 ^ 40 * 1048420 * 2
def baseEnd_1048420 : Nat := 119631863952642952361869

theorem tailTrace_1048420 : CollatzResearch.WordTrace tailWord_1048420 prefixEnd_1048420 119631863952642952361869 := by
  unfold tailWord_1048420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19119509430880435362871357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25492679241173913817161809 19119509430880435362871357)
  ·
    refine ⟨7169816036580163261076759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19119509430880435362871357 7169816036580163261076759)
    ·
      refine ⟨10754724054870244891615139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7169816036580163261076759 10754724054870244891615139)
      ·
        refine ⟨16132086082305367337422709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10754724054870244891615139 16132086082305367337422709)
        ·
          refine ⟨1512383070216128187883379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16132086082305367337422709 1512383070216128187883379)
          ·
            refine ⟨2268574605324192281825069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512383070216128187883379 2268574605324192281825069)
            ·
              refine ⟨850715476996572105684401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2268574605324192281825069 850715476996572105684401)
              ·
                refine ⟨638036607747429079263301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 850715476996572105684401 638036607747429079263301)
                ·
                  refine ⟨119631863952642952361869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638036607747429079263301 119631863952642952361869)
                  ·
                    rfl

theorem cell22_1048420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 1, 3, 2, 4].length) (baseStart_1048420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048420 prefixEnd_1048420 := by exact prefixLift 1048420
  have htrace : WordTrace (prefixWord ++ tailWord_1048420) baseStart_1048420 baseEnd_1048420 := by
    simpa [prefixWord, tailWord_1048420, baseEnd_1048420] using wordTrace_append hprefix tailTrace_1048420
  have hstable : (prefixWord ++ tailWord_1048420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048420).length < 2 ^ (prefixWord ++ tailWord_1048420).sum := by decide
  have hdescent : baseEnd_1048420 < baseStart_1048420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048538 : List Nat := [3, 1, 1, 2, 5, 1, 2, 1, 6]
def baseStart_1048538 : Nat := 118140960795 + 1048538 * 2 ^ 59
def prefixEnd_1048538 : Nat := 4983230072969 + 3 ^ 40 * 1048538 * 2
def baseEnd_1048538 : Nat := 119645328556471960878415

theorem tailTrace_1048538 : CollatzResearch.WordTrace tailWord_1048538 prefixEnd_1048538 119645328556471960878415 := by
  unfold tailWord_1048538
  simp only [CollatzResearch.WordTrace]
  refine ⟨9560830668833344219634567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25495548450222251252358845 9560830668833344219634567)
  ·
    refine ⟨14341246003250016329451851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9560830668833344219634567 14341246003250016329451851)
    ·
      refine ⟨21511869004875024494177777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14341246003250016329451851 21511869004875024494177777)
      ·
        refine ⟨16133901753656268370633333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21511869004875024494177777 16133901753656268370633333)
        ·
          refine ⟨1512553289405275159746875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16133901753656268370633333 1512553289405275159746875)
          ·
            refine ⟨2268829934107912739620313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512553289405275159746875 2268829934107912739620313)
            ·
              refine ⟨1701622450580934554715235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268829934107912739620313 1701622450580934554715235)
              ·
                refine ⟨2552433675871401832072853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701622450580934554715235 2552433675871401832072853)
                ·
                  refine ⟨119645328556471960878415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2552433675871401832072853 119645328556471960878415)
                  ·
                    rfl

theorem cell22_1048538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 1, 6].length) (baseStart_1048538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048538 prefixEnd_1048538 := by exact prefixLift 1048538
  have htrace : WordTrace (prefixWord ++ tailWord_1048538) baseStart_1048538 baseEnd_1048538 := by
    simpa [prefixWord, tailWord_1048538, baseEnd_1048538] using wordTrace_append hprefix tailTrace_1048538
  have hstable : (prefixWord ++ tailWord_1048538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048538).length < 2 ^ (prefixWord ++ tailWord_1048538).sum := by decide
  have hdescent : baseEnd_1048538 < baseStart_1048538 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048557 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 1, 4]
def baseStart_1048557 : Nat := 118140960795 + 1048557 * 2 ^ 59
def prefixEnd_1048557 : Nat := 4983230072969 + 3 ^ 40 * 1048557 * 2
def baseEnd_1048557 : Nat := 358942489757706166410187

theorem tailTrace_1048557 : CollatzResearch.WordTrace tailWord_1048557 prefixEnd_1048557 358942489757706166410187 := by
  unfold tailWord_1048557
  simp only [CollatzResearch.WordTrace]
  refine ⟨38244015662264543123479925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25496010441509695415653283 38244015662264543123479925)
  ·
    refine ⟨3585376468337300917826243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38244015662264543123479925 3585376468337300917826243)
    ·
      refine ⟨5378064702505951376739365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585376468337300917826243 5378064702505951376739365)
      ·
        refine ⟨1008387131719865883138631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5378064702505951376739365 1008387131719865883138631)
        ·
          refine ⟨1512580697579798824707947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008387131719865883138631 1512580697579798824707947)
          ·
            refine ⟨2268871046369698237061921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1512580697579798824707947 2268871046369698237061921)
            ·
              refine ⟨1701653284777273677796441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2268871046369698237061921 1701653284777273677796441)
              ·
                refine ⟨1276239963582955258347331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1701653284777273677796441 1276239963582955258347331)
                ·
                  refine ⟨1914359945374432887520997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276239963582955258347331 1914359945374432887520997)
                  ·
                    refine ⟨358942489757706166410187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1914359945374432887520997 358942489757706166410187)
                    ·
                      rfl

theorem cell22_1048557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 4].length) (baseStart_1048557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048557 prefixEnd_1048557 := by exact prefixLift 1048557
  have htrace : WordTrace (prefixWord ++ tailWord_1048557) baseStart_1048557 baseEnd_1048557 := by
    simpa [prefixWord, tailWord_1048557, baseEnd_1048557] using wordTrace_append hprefix tailTrace_1048557
  have hstable : (prefixWord ++ tailWord_1048557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048557).length < 2 ^ (prefixWord ++ tailWord_1048557).sum := by decide
  have hdescent : baseEnd_1048557 < baseStart_1048557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048589 : List Nat := [1, 7, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1048589 : Nat := 118140960795 + 1048589 * 2 ^ 59
def prefixEnd_1048589 : Nat := 4983230072969 + 3 ^ 40 * 1048589 * 2
def baseEnd_1048589 : Nat := 119651148003889583203363

theorem tailTrace_1048589 : CollatzResearch.WordTrace tailWord_1048589 prefixEnd_1048589 119651148003889583203363 := by
  unfold tailWord_1048589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38245182798148612588644821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25496788532099075059096547 38245182798148612588644821)
  ·
    refine ⟨896371471831608107546363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38245182798148612588644821 896371471831608107546363)
    ·
      refine ⟨1344557207747412161319545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896371471831608107546363 1344557207747412161319545)
      ·
        refine ⟨1008417905810559120989659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1344557207747412161319545 1008417905810559120989659)
        ·
          refine ⟨1512626858715838681484489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1008417905810559120989659 1512626858715838681484489)
          ·
            refine ⟨1134470144036879011113367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1512626858715838681484489 1134470144036879011113367)
            ·
              refine ⟨1701705216055318516670051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1134470144036879011113367 1701705216055318516670051)
              ·
                refine ⟨2552557824082977775005077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1701705216055318516670051 2552557824082977775005077)
                ·
                  refine ⟨119651148003889583203363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2552557824082977775005077 119651148003889583203363)
                  ·
                    rfl

theorem cell22_1048589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1048589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048589 prefixEnd_1048589 := by exact prefixLift 1048589
  have htrace : WordTrace (prefixWord ++ tailWord_1048589) baseStart_1048589 baseEnd_1048589 := by
    simpa [prefixWord, tailWord_1048589, baseEnd_1048589] using wordTrace_append hprefix tailTrace_1048589
  have hstable : (prefixWord ++ tailWord_1048589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048589).length < 2 ^ (prefixWord ++ tailWord_1048589).sum := by decide
  have hdescent : baseEnd_1048589 < baseStart_1048589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048662 : List Nat := [5, 2, 2, 1, 1, 1, 2, 3, 5]
def baseStart_1048662 : Nat := 118140960795 + 1048662 * 2 ^ 59
def prefixEnd_1048662 : Nat := 4983230072969 + 3 ^ 40 * 1048662 * 2
def baseEnd_1048662 : Nat := 119659477801173630844955

theorem tailTrace_1048662 : CollatzResearch.WordTrace tailWord_1048662 prefixEnd_1048662 119659477801173630844955 := by
  unfold tailWord_1048662
  simp only [CollatzResearch.WordTrace]
  refine ⟨2390490332930259128503265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25498563551256097370701493 2390490332930259128503265)
  ·
    refine ⟨1792867749697694346377449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2390490332930259128503265 1792867749697694346377449)
    ·
      refine ⟨1344650812273270759783087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1792867749697694346377449 1344650812273270759783087)
      ·
        refine ⟨2016976218409906139674631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1344650812273270759783087 2016976218409906139674631)
        ·
          refine ⟨3025464327614859209511947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2016976218409906139674631 3025464327614859209511947)
          ·
            refine ⟨4538196491422288814267921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025464327614859209511947 4538196491422288814267921)
            ·
              refine ⟨3403647368566716610700941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538196491422288814267921 3403647368566716610700941)
              ·
                refine ⟨1276367763212518729012853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3403647368566716610700941 1276367763212518729012853)
                ·
                  refine ⟨119659477801173630844955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276367763212518729012853 119659477801173630844955)
                  ·
                    rfl

theorem cell22_1048662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 3, 5].length) (baseStart_1048662 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048662 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048662 prefixEnd_1048662 := by exact prefixLift 1048662
  have htrace : WordTrace (prefixWord ++ tailWord_1048662) baseStart_1048662 baseEnd_1048662 := by
    simpa [prefixWord, tailWord_1048662, baseEnd_1048662] using wordTrace_append hprefix tailTrace_1048662
  have hstable : (prefixWord ++ tailWord_1048662).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048662).length < 2 ^ (prefixWord ++ tailWord_1048662).sum := by decide
  have hdescent : baseEnd_1048662 < baseStart_1048662 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048688 : List Nat := [2, 1, 1, 1, 5, 2, 2, 2, 1, 5]
def baseStart_1048688 : Nat := 118140960795 + 1048688 * 2 ^ 59
def prefixEnd_1048688 : Nat := 4983230072969 + 3 ^ 40 * 1048688 * 2
def baseEnd_1048688 : Nat := 358987333734865491384785

theorem tailTrace_1048688 : CollatzResearch.WordTrace tailWord_1048688 prefixEnd_1048688 358987333734865491384785 := by
  unfold tailWord_1048688
  simp only [CollatzResearch.WordTrace]
  refine ⟨19124396812394976248249359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25499195749859968330999145 19124396812394976248249359)
  ·
    refine ⟨28686595218592464372374039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19124396812394976248249359 28686595218592464372374039)
    ·
      refine ⟨43029892827888696558561059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28686595218592464372374039 43029892827888696558561059)
      ·
        refine ⟨64544839241833044837841589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43029892827888696558561059 64544839241833044837841589)
        ·
          refine ⟨6051078678921847953547649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64544839241833044837841589 6051078678921847953547649)
          ·
            refine ⟨4538309009191385965160737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6051078678921847953547649 4538309009191385965160737)
            ·
              refine ⟨3403731756893539473870553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538309009191385965160737 3403731756893539473870553)
              ·
                refine ⟨2552798817670154605402915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3403731756893539473870553 2552798817670154605402915)
                ·
                  refine ⟨3829198226505231908104373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552798817670154605402915 3829198226505231908104373)
                  ·
                    refine ⟨358987333734865491384785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3829198226505231908104373 358987333734865491384785)
                    ·
                      rfl

theorem cell22_1048688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 2, 2, 1, 5].length) (baseStart_1048688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048688 prefixEnd_1048688 := by exact prefixLift 1048688
  have htrace : WordTrace (prefixWord ++ tailWord_1048688) baseStart_1048688 baseEnd_1048688 := by
    simpa [prefixWord, tailWord_1048688, baseEnd_1048688] using wordTrace_append hprefix tailTrace_1048688
  have hstable : (prefixWord ++ tailWord_1048688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048688).length < 2 ^ (prefixWord ++ tailWord_1048688).sum := by decide
  have hdescent : baseEnd_1048688 < baseStart_1048688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048690 : List Nat := [3, 2, 1, 2, 2, 2, 1, 5, 4]
def baseStart_1048690 : Nat := 118140960795 + 1048690 * 2 ^ 59
def prefixEnd_1048690 : Nat := 4983230072969 + 3 ^ 40 * 1048690 * 2
def baseEnd_1048690 : Nat := 119662672791912717611593

theorem tailTrace_1048690 : CollatzResearch.WordTrace tailWord_1048690 prefixEnd_1048690 119662672791912717611593 := by
  unfold tailWord_1048690
  simp only [CollatzResearch.WordTrace]
  refine ⟨9562216642695676709517881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25499244380521804558714349 9562216642695676709517881)
  ·
    refine ⟨7171662482021757532138411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9562216642695676709517881 7171662482021757532138411)
    ·
      refine ⟨10757493723032636298207617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7171662482021757532138411 10757493723032636298207617)
      ·
        refine ⟨8068120292274477223655713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10757493723032636298207617 8068120292274477223655713)
        ·
          refine ⟨6051090219205857917741785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8068120292274477223655713 6051090219205857917741785)
          ·
            refine ⟨4538317664404393438306339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6051090219205857917741785 4538317664404393438306339)
            ·
              refine ⟨6807476496606590157459509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538317664404393438306339 6807476496606590157459509)
              ·
                refine ⟨638200921556867827261829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6807476496606590157459509 638200921556867827261829)
                ·
                  refine ⟨119662672791912717611593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638200921556867827261829 119662672791912717611593)
                  ·
                    rfl

theorem cell22_1048690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 2, 1, 5, 4].length) (baseStart_1048690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048690 prefixEnd_1048690 := by exact prefixLift 1048690
  have htrace : WordTrace (prefixWord ++ tailWord_1048690) baseStart_1048690 baseEnd_1048690 := by
    simpa [prefixWord, tailWord_1048690, baseEnd_1048690] using wordTrace_append hprefix tailTrace_1048690
  have hstable : (prefixWord ++ tailWord_1048690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048690).length < 2 ^ (prefixWord ++ tailWord_1048690).sum := by decide
  have hdescent : baseEnd_1048690 < baseStart_1048690 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048735 : List Nat := [1, 1, 2, 6, 1, 1, 4, 6]
def baseStart_1048735 : Nat := 118140960795 + 1048735 * 2 ^ 59
def prefixEnd_1048735 : Nat := 4983230072969 + 3 ^ 40 * 1048735 * 2
def baseEnd_1048735 : Nat := 39889269199485892828849

theorem tailTrace_1048735 : CollatzResearch.WordTrace tailWord_1048735 prefixEnd_1048735 39889269199485892828849 := by
  unfold tailWord_1048735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38250507855619679523459659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25500338570413119682306439 38250507855619679523459659)
  ·
    refine ⟨57375761783429519285189489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38250507855619679523459659 57375761783429519285189489)
    ·
      refine ⟨43031821337572139463892117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57375761783429519285189489 43031821337572139463892117)
      ·
        refine ⟨2017116625198694037369943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 43031821337572139463892117 2017116625198694037369943)
        ·
          refine ⟨3025674937798041056054915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017116625198694037369943 3025674937798041056054915)
          ·
            refine ⟨4538512406697061584082373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025674937798041056054915 4538512406697061584082373)
            ·
              refine ⟨850971076255699047015445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4538512406697061584082373 850971076255699047015445)
              ·
                refine ⟨39889269199485892828849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 850971076255699047015445 39889269199485892828849)
                ·
                  rfl

theorem cell22_1048735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 4, 6].length) (baseStart_1048735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048735 prefixEnd_1048735 := by exact prefixLift 1048735
  have htrace : WordTrace (prefixWord ++ tailWord_1048735) baseStart_1048735 baseEnd_1048735 := by
    simpa [prefixWord, tailWord_1048735, baseEnd_1048735] using wordTrace_append hprefix tailTrace_1048735
  have hstable : (prefixWord ++ tailWord_1048735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048735).length < 2 ^ (prefixWord ++ tailWord_1048735).sum := by decide
  have hdescent : baseEnd_1048735 < baseStart_1048735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048763 : List Nat := [1, 1, 1, 1, 1, 2, 6, 4, 5]
def baseStart_1048763 : Nat := 118140960795 + 1048763 * 2 ^ 59
def prefixEnd_1048763 : Nat := 4983230072969 + 3 ^ 40 * 1048763 * 2
def baseEnd_1048763 : Nat := 119671002589196765253185

theorem tailTrace_1048763 : CollatzResearch.WordTrace tailWord_1048763 prefixEnd_1048763 119671002589196765253185 := by
  unfold tailWord_1048763
  simp only [CollatzResearch.WordTrace]
  refine ⟨38251529099518240305478943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25501019399678826870319295 38251529099518240305478943)
  ·
    refine ⟨57377293649277360458218415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38251529099518240305478943 57377293649277360458218415)
    ·
      refine ⟨86065940473916040687327623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57377293649277360458218415 86065940473916040687327623)
      ·
        refine ⟨129098910710874061030991435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86065940473916040687327623 129098910710874061030991435)
        ·
          refine ⟨193648366066311091546487153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129098910710874061030991435 193648366066311091546487153)
          ·
            refine ⟨145236274549733318659865365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193648366066311091546487153 145236274549733318659865365)
            ·
              refine ⟨6807950369518749312181189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 145236274549733318659865365 6807950369518749312181189)
              ·
                refine ⟨1276490694284765496033973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6807950369518749312181189 1276490694284765496033973)
                ·
                  refine ⟨119671002589196765253185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276490694284765496033973 119671002589196765253185)
                  ·
                    rfl

theorem cell22_1048763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 4, 5].length) (baseStart_1048763 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048763 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048763 prefixEnd_1048763 := by exact prefixLift 1048763
  have htrace : WordTrace (prefixWord ++ tailWord_1048763) baseStart_1048763 baseEnd_1048763 := by
    simpa [prefixWord, tailWord_1048763, baseEnd_1048763] using wordTrace_append hprefix tailTrace_1048763
  have hstable : (prefixWord ++ tailWord_1048763).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048763).length < 2 ^ (prefixWord ++ tailWord_1048763).sum := by decide
  have hdescent : baseEnd_1048763 < baseStart_1048763 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048778 : List Nat := [3, 1, 2, 1, 3, 1, 2, 1, 1, 7]
def baseStart_1048778 : Nat := 118140960795 + 1048778 * 2 ^ 59
def prefixEnd_1048778 : Nat := 4983230072969 + 3 ^ 40 * 1048778 * 2
def baseEnd_1048778 : Nat := 359018142574135256634509

theorem tailTrace_1048778 : CollatzResearch.WordTrace tailWord_1048778 prefixEnd_1048778 359018142574135256634509 := by
  unfold tailWord_1048778
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563019048615974466818747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25501384129642598578183325 9563019048615974466818747)
  ·
    refine ⟨14344528572923961700228121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9563019048615974466818747 14344528572923961700228121)
    ·
      refine ⟨10758396429692971275171091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14344528572923961700228121 10758396429692971275171091)
      ·
        refine ⟨16137594644539456912756637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10758396429692971275171091 16137594644539456912756637)
        ·
          refine ⟨6051597991702296342283739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16137594644539456912756637 6051597991702296342283739)
          ·
            refine ⟨9077396987553444513425609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051597991702296342283739 9077396987553444513425609)
            ·
              refine ⟨6808047740665083385069207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9077396987553444513425609 6808047740665083385069207)
              ·
                refine ⟨10212071610997625077603811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6808047740665083385069207 10212071610997625077603811)
                ·
                  refine ⟨15318107416496437616405717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10212071610997625077603811 15318107416496437616405717)
                  ·
                    refine ⟨359018142574135256634509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15318107416496437616405717 359018142574135256634509)
                    ·
                      rfl

theorem cell22_1048778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_1048778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048778 prefixEnd_1048778 := by exact prefixLift 1048778
  have htrace : WordTrace (prefixWord ++ tailWord_1048778) baseStart_1048778 baseEnd_1048778 := by
    simpa [prefixWord, tailWord_1048778, baseEnd_1048778] using wordTrace_append hprefix tailTrace_1048778
  have hstable : (prefixWord ++ tailWord_1048778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048778).length < 2 ^ (prefixWord ++ tailWord_1048778).sum := by decide
  have hdescent : baseEnd_1048778 < baseStart_1048778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048840 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 1, 5]
def baseStart_1048840 : Nat := 118140960795 + 1048840 * 2 ^ 59
def prefixEnd_1048840 : Nat := 4983230072969 + 3 ^ 40 * 1048840 * 2
def baseEnd_1048840 : Nat := 359039366441187761584319

theorem tailTrace_1048840 : CollatzResearch.WordTrace tailWord_1048840 prefixEnd_1048840 359039366441187761584319 := by
  unfold tailWord_1048840
  simp only [CollatzResearch.WordTrace]
  refine ⟨19127168760119641228015987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25502891680159521637354649 19127168760119641228015987)
  ·
    refine ⟨28690753140179461842023981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19127168760119641228015987 28690753140179461842023981)
    ·
      refine ⟨10759032427567298190758993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28690753140179461842023981 10759032427567298190758993)
      ·
        refine ⟨8069274320675473643069245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10759032427567298190758993 8069274320675473643069245)
        ·
          refine ⟨3025977870253302616150967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8069274320675473643069245 3025977870253302616150967)
          ·
            refine ⟨4538966805379953924226451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025977870253302616150967 4538966805379953924226451)
            ·
              refine ⟨6808450208069930886339677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538966805379953924226451 6808450208069930886339677)
              ·
                refine ⟨2553168828026224082377379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6808450208069930886339677 2553168828026224082377379)
                ·
                  refine ⟨3829753242039336123566069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553168828026224082377379 3829753242039336123566069)
                  ·
                    refine ⟨359039366441187761584319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3829753242039336123566069 359039366441187761584319)
                    ·
                      rfl

theorem cell22_1048840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 5].length) (baseStart_1048840 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048840 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048840 prefixEnd_1048840 := by exact prefixLift 1048840
  have htrace : WordTrace (prefixWord ++ tailWord_1048840) baseStart_1048840 baseEnd_1048840 := by
    simpa [prefixWord, tailWord_1048840, baseEnd_1048840] using wordTrace_append hprefix tailTrace_1048840
  have hstable : (prefixWord ++ tailWord_1048840).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048840).length < 2 ^ (prefixWord ++ tailWord_1048840).sum := by decide
  have hdescent : baseEnd_1048840 < baseStart_1048840 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048853 : List Nat := [1, 3, 2, 1, 2, 1, 2, 10]
def baseStart_1048853 : Nat := 118140960795 + 1048853 * 2 ^ 59
def prefixEnd_1048853 : Nat := 4983230072969 + 3 ^ 40 * 1048853 * 2
def baseEnd_1048853 : Nat := 39893757400762229001031

theorem tailTrace_1048853 : CollatzResearch.WordTrace tailWord_1048853 prefixEnd_1048853 39893757400762229001031 := by
  unfold tailWord_1048853
  simp only [CollatzResearch.WordTrace]
  refine ⟨38254811669192185676255213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25503207779461457117503475 38254811669192185676255213)
  ·
    refine ⟨14345554375947069628595705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38254811669192185676255213 14345554375947069628595705)
    ·
      refine ⟨10759165781960302221446779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14345554375947069628595705 10759165781960302221446779)
      ·
        refine ⟨16138748672940453332170169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10759165781960302221446779 16138748672940453332170169)
        ·
          refine ⟨12104061504705339999127627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16138748672940453332170169 12104061504705339999127627)
          ·
            refine ⟨18156092257058009998691441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12104061504705339999127627 18156092257058009998691441)
            ·
              refine ⟨13617069192793507499018581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18156092257058009998691441 13617069192793507499018581)
              ·
                refine ⟨39893757400762229001031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 13617069192793507499018581 39893757400762229001031)
                ·
                  rfl

theorem cell22_1048853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 10].length) (baseStart_1048853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048853 prefixEnd_1048853 := by exact prefixLift 1048853
  have htrace : WordTrace (prefixWord ++ tailWord_1048853) baseStart_1048853 baseEnd_1048853 := by
    simpa [prefixWord, tailWord_1048853, baseEnd_1048853] using wordTrace_append hprefix tailTrace_1048853
  have hstable : (prefixWord ++ tailWord_1048853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048853).length < 2 ^ (prefixWord ++ tailWord_1048853).sum := by decide
  have hdescent : baseEnd_1048853 < baseStart_1048853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048855 : List Nat := [1, 1, 3, 4, 1, 3, 1, 1, 1, 6]
def baseStart_1048855 : Nat := 118140960795 + 1048855 * 2 ^ 59
def prefixEnd_1048855 : Nat := 4983230072969 + 3 ^ 40 * 1048855 * 2
def baseEnd_1048855 : Nat := 359044501247732722459273

theorem tailTrace_1048855 : CollatzResearch.WordTrace tailWord_1048855 prefixEnd_1048855 359044501247732722459273 := by
  unfold tailWord_1048855
  simp only [CollatzResearch.WordTrace]
  refine ⟨38254884615184940017828019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25503256410123293345218679 38254884615184940017828019)
  ·
    refine ⟨57382326922777410026742029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38254884615184940017828019 57382326922777410026742029)
    ·
      refine ⟨21518372596041528760028261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57382326922777410026742029 21518372596041528760028261)
      ·
        refine ⟨4034694861757786642505299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21518372596041528760028261 4034694861757786642505299)
        ·
          refine ⟨6052042292636679963757949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034694861757786642505299 6052042292636679963757949)
          ·
            refine ⟨2269515859738754986409231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6052042292636679963757949 2269515859738754986409231)
            ·
              refine ⟨3404273789608132479613847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269515859738754986409231 3404273789608132479613847)
              ·
                refine ⟨5106410684412198719420771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404273789608132479613847 5106410684412198719420771)
                ·
                  refine ⟨7659616026618298079131157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106410684412198719420771 7659616026618298079131157)
                  ·
                    refine ⟨359044501247732722459273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7659616026618298079131157 359044501247732722459273)
                    ·
                      rfl

theorem cell22_1048855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 3, 1, 1, 1, 6].length) (baseStart_1048855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048855 prefixEnd_1048855 := by exact prefixLift 1048855
  have htrace : WordTrace (prefixWord ++ tailWord_1048855) baseStart_1048855 baseEnd_1048855 := by
    simpa [prefixWord, tailWord_1048855, baseEnd_1048855] using wordTrace_append hprefix tailTrace_1048855
  have hstable : (prefixWord ++ tailWord_1048855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048855).length < 2 ^ (prefixWord ++ tailWord_1048855).sum := by decide
  have hdescent : baseEnd_1048855 < baseStart_1048855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048861 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 1, 4]
def baseStart_1048861 : Nat := 118140960795 + 1048861 * 2 ^ 59
def prefixEnd_1048861 : Nat := 4983230072969 + 3 ^ 40 * 1048861 * 2
def baseEnd_1048861 : Nat := 359046555170350706809255

theorem tailTrace_1048861 : CollatzResearch.WordTrace tailWord_1048861 prefixEnd_1048861 359046555170350706809255 := by
  unfold tailWord_1048861
  simp only [CollatzResearch.WordTrace]
  refine ⟨38255103453163203042546437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25503402302108802028364291 38255103453163203042546437)
  ·
    refine ⟨7172831897468100570477457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38255103453163203042546437 7172831897468100570477457)
    ·
      refine ⟨5379623923101075427858093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7172831897468100570477457 5379623923101075427858093)
      ·
        refine ⟨2017358971162903285446785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5379623923101075427858093 2017358971162903285446785)
        ·
          refine ⟨1513019228372177464085089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017358971162903285446785 1513019228372177464085089)
          ·
            refine ⟨1134764421279133098063817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513019228372177464085089 1134764421279133098063817)
            ·
              refine ⟨851073315959349823547863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1134764421279133098063817 851073315959349823547863)
              ·
                refine ⟨1276609973939024735321795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851073315959349823547863 1276609973939024735321795)
                ·
                  refine ⟨1914914960908537102982693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1276609973939024735321795 1914914960908537102982693)
                  ·
                    refine ⟨359046555170350706809255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1914914960908537102982693 359046555170350706809255)
                    ·
                      rfl

theorem cell22_1048861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 4].length) (baseStart_1048861 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048861 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048861 prefixEnd_1048861 := by exact prefixLift 1048861
  have htrace : WordTrace (prefixWord ++ tailWord_1048861) baseStart_1048861 baseEnd_1048861 := by
    simpa [prefixWord, tailWord_1048861, baseEnd_1048861] using wordTrace_append hprefix tailTrace_1048861
  have hstable : (prefixWord ++ tailWord_1048861).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048861).length < 2 ^ (prefixWord ++ tailWord_1048861).sum := by decide
  have hdescent : baseEnd_1048861 < baseStart_1048861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048874 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 4, 3]
def baseStart_1048874 : Nat := 118140960795 + 1048874 * 2 ^ 59
def prefixEnd_1048874 : Nat := 4983230072969 + 3 ^ 40 * 1048874 * 2
def baseEnd_1048874 : Nat := 359051005336023006234215

theorem tailTrace_1048874 : CollatzResearch.WordTrace tailWord_1048874 prefixEnd_1048874 359051005336023006234215 := by
  unfold tailWord_1048874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9563894400529026565692419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25503718401410737508513117 9563894400529026565692419)
  ·
    refine ⟨14345841600793539848538629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9563894400529026565692419 14345841600793539848538629)
    ·
      refine ⟨2689845300148788721600993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14345841600793539848538629 2689845300148788721600993)
      ·
        refine ⟨2017383975111591541200745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2689845300148788721600993 2017383975111591541200745)
        ·
          refine ⟨1513037981333693655900559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2017383975111591541200745 1513037981333693655900559)
          ·
            refine ⟨2269556972000540483850839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513037981333693655900559 2269556972000540483850839)
            ·
              refine ⟨3404335458000810725776259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2269556972000540483850839 3404335458000810725776259)
              ·
                refine ⟨5106503187001216088664389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404335458000810725776259 5106503187001216088664389)
                ·
                  refine ⟨957469347562728016624573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5106503187001216088664389 957469347562728016624573)
                  ·
                    refine ⟨359051005336023006234215, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957469347562728016624573 359051005336023006234215)
                    ·
                      rfl

theorem cell22_1048874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 3].length) (baseStart_1048874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048874 prefixEnd_1048874 := by exact prefixLift 1048874
  have htrace : WordTrace (prefixWord ++ tailWord_1048874) baseStart_1048874 baseEnd_1048874 := by
    simpa [prefixWord, tailWord_1048874, baseEnd_1048874] using wordTrace_append hprefix tailTrace_1048874
  have hstable : (prefixWord ++ tailWord_1048874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048874).length < 2 ^ (prefixWord ++ tailWord_1048874).sum := by decide
  have hdescent : baseEnd_1048874 < baseStart_1048874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048945 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 3, 4]
def baseStart_1048945 : Nat := 118140960795 + 1048945 * 2 ^ 59
def prefixEnd_1048945 : Nat := 4983230072969 + 3 ^ 40 * 1048945 * 2
def baseEnd_1048945 : Nat := 359075310087002487708997

theorem tailTrace_1048945 : CollatzResearch.WordTrace tailWord_1048945 prefixEnd_1048945 359075310087002487708997 := by
  unfold tailWord_1048945
  simp only [CollatzResearch.WordTrace]
  refine ⟨38258167184858885388604289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25505444789905923592402859 38258167184858885388604289)
  ·
    refine ⟨28693625388644164041453217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38258167184858885388604289 28693625388644164041453217)
    ·
      refine ⟨21520219041483123031089913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28693625388644164041453217 21520219041483123031089913)
      ·
        refine ⟨16140164281112342273317435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21520219041483123031089913 16140164281112342273317435)
        ·
          refine ⟨24210246421668513409976153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16140164281112342273317435 24210246421668513409976153)
          ·
            refine ⟨18157684816251385057482115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24210246421668513409976153 18157684816251385057482115)
            ·
              refine ⟨27236527224377077586223173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18157684816251385057482115 27236527224377077586223173)
              ·
                refine ⟨5106848854570702047416845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27236527224377077586223173 5106848854570702047416845)
                ·
                  refine ⟨1915068320464013267781317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5106848854570702047416845 1915068320464013267781317)
                  ·
                    refine ⟨359075310087002487708997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915068320464013267781317 359075310087002487708997)
                    ·
                      rfl

theorem cell22_1048945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 3, 4].length) (baseStart_1048945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048945 prefixEnd_1048945 := by exact prefixLift 1048945
  have htrace : WordTrace (prefixWord ++ tailWord_1048945) baseStart_1048945 baseEnd_1048945 := by
    simpa [prefixWord, tailWord_1048945, baseEnd_1048945] using wordTrace_append hprefix tailTrace_1048945
  have hstable : (prefixWord ++ tailWord_1048945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048945).length < 2 ^ (prefixWord ++ tailWord_1048945).sum := by decide
  have hdescent : baseEnd_1048945 < baseStart_1048945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048949 : List Nat := [1, 3, 4, 1, 2, 1, 4, 1, 5]
def baseStart_1048949 : Nat := 118140960795 + 1048949 * 2 ^ 59
def prefixEnd_1048949 : Nat := 4983230072969 + 3 ^ 40 * 1048949 * 2
def baseEnd_1048949 : Nat := 119692226456249270202995

theorem tailTrace_1048949 : CollatzResearch.WordTrace tailWord_1048949 prefixEnd_1048949 119692226456249270202995 := by
  unfold tailWord_1048949
  simp only [CollatzResearch.WordTrace]
  refine ⟨38258313076844394071749901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25505542051229596047833267 38258313076844394071749901)
  ·
    refine ⟨14346867403816647776906213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38258313076844394071749901 14346867403816647776906213)
    ·
      refine ⟨2690037638215621458169915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14346867403816647776906213 2690037638215621458169915)
      ·
        refine ⟨4035056457323432187254873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2690037638215621458169915 4035056457323432187254873)
        ·
          refine ⟨3026292342992574140441155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4035056457323432187254873 3026292342992574140441155)
          ·
            refine ⟨4539438514488861210661733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026292342992574140441155 4539438514488861210661733)
            ·
              refine ⟨851144721466661476999075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4539438514488861210661733 851144721466661476999075)
              ·
                refine ⟨1276717082199992215498613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851144721466661476999075 1276717082199992215498613)
                ·
                  refine ⟨119692226456249270202995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1276717082199992215498613 119692226456249270202995)
                  ·
                    rfl

theorem cell22_1048949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 4, 1, 5].length) (baseStart_1048949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048949 prefixEnd_1048949 := by exact prefixLift 1048949
  have htrace : WordTrace (prefixWord ++ tailWord_1048949) baseStart_1048949 baseEnd_1048949 := by
    simpa [prefixWord, tailWord_1048949, baseEnd_1048949] using wordTrace_append hprefix tailTrace_1048949
  have hstable : (prefixWord ++ tailWord_1048949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048949).length < 2 ^ (prefixWord ++ tailWord_1048949).sum := by decide
  have hdescent : baseEnd_1048949 < baseStart_1048949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1048994 : List Nat := [3, 3, 1, 2, 1, 1, 3, 4, 4]
def baseStart_1048994 : Nat := 118140960795 + 1048994 * 2 ^ 59
def prefixEnd_1048994 : Nat := 4983230072969 + 3 ^ 40 * 1048994 * 2
def baseEnd_1048994 : Nat := 119697361262794231077949

theorem tailTrace_1048994 : CollatzResearch.WordTrace tailWord_1048994 prefixEnd_1048994 119697361262794231077949 := by
  unfold tailWord_1048994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564988590420341689284509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25506636241120911171425357 9564988590420341689284509)
  ·
    refine ⟨3586870721407628133481691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9564988590420341689284509 3586870721407628133481691)
    ·
      refine ⟨5380306082111442200222537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3586870721407628133481691 5380306082111442200222537)
      ·
        refine ⟨4035229561583581650166903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5380306082111442200222537 4035229561583581650166903)
        ·
          refine ⟨6052844342375372475250355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035229561583581650166903 6052844342375372475250355)
          ·
            refine ⟨9079266513563058712875533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052844342375372475250355 9079266513563058712875533)
            ·
              refine ⟨3404724942586147017328325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9079266513563058712875533 3404724942586147017328325)
              ·
                refine ⟨638385926734902565749061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3404724942586147017328325 638385926734902565749061)
                ·
                  refine ⟨119697361262794231077949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638385926734902565749061 119697361262794231077949)
                  ·
                    rfl

theorem cell22_1048994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 3, 4, 4].length) (baseStart_1048994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1048994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1048994 prefixEnd_1048994 := by exact prefixLift 1048994
  have htrace : WordTrace (prefixWord ++ tailWord_1048994) baseStart_1048994 baseEnd_1048994 := by
    simpa [prefixWord, tailWord_1048994, baseEnd_1048994] using wordTrace_append hprefix tailTrace_1048994
  have hstable : (prefixWord ++ tailWord_1048994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1048994).length < 2 ^ (prefixWord ++ tailWord_1048994).sum := by decide
  have hdescent : baseEnd_1048994 < baseStart_1048994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1048994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049009 : List Nat := [1, 2, 2, 4, 1, 2, 2, 3, 2, 3]
def baseStart_1049009 : Nat := 118140960795 + 1049009 * 2 ^ 59
def prefixEnd_1049009 : Nat := 4983230072969 + 3 ^ 40 * 1049009 * 2
def baseEnd_1049009 : Nat := 359097218594927654108801

theorem tailTrace_1049009 : CollatzResearch.WordTrace tailWord_1049009 prefixEnd_1049009 359097218594927654108801 := by
  unfold tailWord_1049009
  simp only [CollatzResearch.WordTrace]
  refine ⟨38260501456627024318934081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25507000971084682879289387 38260501456627024318934081)
  ·
    refine ⟨28695376092470268239200561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38260501456627024318934081 28695376092470268239200561)
    ·
      refine ⟨21521532069352701179400421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28695376092470268239200561 21521532069352701179400421)
      ·
        refine ⟨4035287263003631471137579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21521532069352701179400421 4035287263003631471137579)
        ·
          refine ⟨6052930894505447206706369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035287263003631471137579 6052930894505447206706369)
          ·
            refine ⟨4539698170879085405029777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6052930894505447206706369 4539698170879085405029777)
            ·
              refine ⟨3404773628159314053772333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4539698170879085405029777 3404773628159314053772333)
              ·
                refine ⟨1276790110559742770164625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3404773628159314053772333 1276790110559742770164625)
                ·
                  refine ⟨957592582919807077623469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1276790110559742770164625 957592582919807077623469)
                  ·
                    refine ⟨359097218594927654108801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957592582919807077623469 359097218594927654108801)
                    ·
                      rfl

theorem cell22_1049009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 3, 2, 3].length) (baseStart_1049009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049009 prefixEnd_1049009 := by exact prefixLift 1049009
  have htrace : WordTrace (prefixWord ++ tailWord_1049009) baseStart_1049009 baseEnd_1049009 := by
    simpa [prefixWord, tailWord_1049009, baseEnd_1049009] using wordTrace_append hprefix tailTrace_1049009
  have hstable : (prefixWord ++ tailWord_1049009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049009).length < 2 ^ (prefixWord ++ tailWord_1049009).sum := by decide
  have hdescent : baseEnd_1049009 < baseStart_1049009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049065 : List Nat := [1, 2, 1, 1, 1, 2, 1, 5, 1, 7]
def baseStart_1049065 : Nat := 118140960795 + 1049065 * 2 ^ 59
def prefixEnd_1049065 : Nat := 4983230072969 + 3 ^ 40 * 1049065 * 2
def baseEnd_1049065 : Nat := 359116388539362174708629

theorem tailTrace_1049065 : CollatzResearch.WordTrace tailWord_1049065 prefixEnd_1049065 359116388539362174708629 := by
  unfold tailWord_1049065
  simp only [CollatzResearch.WordTrace]
  refine ⟨38262543944424145882972649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25508362629616097255315099 38262543944424145882972649)
  ·
    refine ⟨28696907958318109412229487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38262543944424145882972649 28696907958318109412229487)
    ·
      refine ⟨43045361937477164118344231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28696907958318109412229487 43045361937477164118344231)
      ·
        refine ⟨64568042906215746177516347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43045361937477164118344231 64568042906215746177516347)
        ·
          refine ⟨96852064359323619266274521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64568042906215746177516347 96852064359323619266274521)
          ·
            refine ⟨72639048269492714449705891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96852064359323619266274521 72639048269492714449705891)
            ·
              refine ⟨108958572404239071674558837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72639048269492714449705891 108958572404239071674558837)
              ·
                refine ⟨10214866162897412969489891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108958572404239071674558837 10214866162897412969489891)
                ·
                  refine ⟨15322299244346119454234837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10214866162897412969489891 15322299244346119454234837)
                  ·
                    refine ⟨359116388539362174708629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15322299244346119454234837 359116388539362174708629)
                    ·
                      rfl

theorem cell22_1049065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 1, 7].length) (baseStart_1049065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049065 prefixEnd_1049065 := by exact prefixLift 1049065
  have htrace : WordTrace (prefixWord ++ tailWord_1049065) baseStart_1049065 baseEnd_1049065 := by
    simpa [prefixWord, tailWord_1049065, baseEnd_1049065] using wordTrace_append hprefix tailTrace_1049065
  have hstable : (prefixWord ++ tailWord_1049065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049065).length < 2 ^ (prefixWord ++ tailWord_1049065).sum := by decide
  have hdescent : baseEnd_1049065 < baseStart_1049065 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049101 : List Nat := [1, 7, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1049101 : Nat := 118140960795 + 1049101 * 2 ^ 59
def prefixEnd_1049101 : Nat := 4983230072969 + 3 ^ 40 * 1049101 * 2
def baseEnd_1049101 : Nat := 119709570691690026936173

theorem tailTrace_1049101 : CollatzResearch.WordTrace tailWord_1049101 prefixEnd_1049101 119709570691690026936173 := by
  unfold tailWord_1049101
  simp only [CollatzResearch.WordTrace]
  refine ⟨38263856972293724031283157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25509237981529149354188771 38263856972293724031283157)
  ·
    refine ⟨896809147788134156983199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38263856972293724031283157 896809147788134156983199)
    ·
      refine ⟨1345213721682201235474799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 896809147788134156983199 1345213721682201235474799)
      ·
        refine ⟨2017820582523301853212199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345213721682201235474799 2017820582523301853212199)
        ·
          refine ⟨3026730873784952779818299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2017820582523301853212199 3026730873784952779818299)
          ·
            refine ⟨4540096310677429169727449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026730873784952779818299 4540096310677429169727449)
            ·
              refine ⟨3405072233008071877295587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540096310677429169727449 3405072233008071877295587)
              ·
                refine ⟨5107608349512107815943381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405072233008071877295587 5107608349512107815943381)
                ·
                  refine ⟨119709570691690026936173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5107608349512107815943381 119709570691690026936173)
                  ·
                    rfl

theorem cell22_1049101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1049101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049101 prefixEnd_1049101 := by exact prefixLift 1049101
  have htrace : WordTrace (prefixWord ++ tailWord_1049101) baseStart_1049101 baseEnd_1049101 := by
    simpa [prefixWord, tailWord_1049101, baseEnd_1049101] using wordTrace_append hprefix tailTrace_1049101
  have hstable : (prefixWord ++ tailWord_1049101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049101).length < 2 ^ (prefixWord ++ tailWord_1049101).sum := by decide
  have hdescent : baseEnd_1049101 < baseStart_1049101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049156 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1049156 : Nat := 118140960795 + 1049156 * 2 ^ 59
def prefixEnd_1049156 : Nat := 4983230072969 + 3 ^ 40 * 1049156 * 2
def baseEnd_1049156 : Nat := 359147539699068270683351

theorem tailTrace_1049156 : CollatzResearch.WordTrace tailWord_1049156 prefixEnd_1049156 359147539699068270683351 := by
  unfold tailWord_1049156
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132931493547234212267661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25510575324729645616356881 19132931493547234212267661)
  ·
    refine ⟨7174849310080212829600373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19132931493547234212267661 7174849310080212829600373)
    ·
      refine ⟨672642122820019952775035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 7174849310080212829600373 672642122820019952775035)
      ·
        refine ⟨1008963184230029929162553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 672642122820019952775035 1008963184230029929162553)
        ·
          refine ⟨756722388172522446871915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1008963184230029929162553 756722388172522446871915)
          ·
            refine ⟨1135083582258783670307873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756722388172522446871915 1135083582258783670307873)
            ·
              refine ⟨851312686694087752730905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135083582258783670307873 851312686694087752730905)
              ·
                refine ⟨638484515020565814548179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 851312686694087752730905 638484515020565814548179)
                ·
                  refine ⟨957726772530848721822269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638484515020565814548179 957726772530848721822269)
                  ·
                    refine ⟨359147539699068270683351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957726772530848721822269 359147539699068270683351)
                    ·
                      rfl

theorem cell22_1049156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1049156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049156 prefixEnd_1049156 := by exact prefixLift 1049156
  have htrace : WordTrace (prefixWord ++ tailWord_1049156) baseStart_1049156 baseEnd_1049156 := by
    simpa [prefixWord, tailWord_1049156, baseEnd_1049156] using wordTrace_append hprefix tailTrace_1049156
  have hstable : (prefixWord ++ tailWord_1049156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049156).length < 2 ^ (prefixWord ++ tailWord_1049156).sum := by decide
  have hdescent : baseEnd_1049156 < baseStart_1049156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049159 : List Nat := [1, 1, 4, 1, 4, 1, 2, 2, 2, 4]
def baseStart_1049159 : Nat := 118140960795 + 1049159 * 2 ^ 59
def prefixEnd_1049159 : Nat := 4983230072969 + 3 ^ 40 * 1049159 * 2
def baseEnd_1049159 : Nat := 359148566660377262858341

theorem tailTrace_1049159 : CollatzResearch.WordTrace tailWord_1049159 prefixEnd_1049159 359148566660377262858341 := by
  unfold tailWord_1049159
  simp only [CollatzResearch.WordTrace]
  refine ⟨38265972406083599936894531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25510648270722399957929687 38265972406083599936894531)
  ·
    refine ⟨57398958609125399905341797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38265972406083599936894531 57398958609125399905341797)
    ·
      refine ⟨10762304739211012482251587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57398958609125399905341797 10762304739211012482251587)
      ·
        refine ⟨16143457108816518723377381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10762304739211012482251587 16143457108816518723377381)
        ·
          refine ⟨3026898207903097260633259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16143457108816518723377381 3026898207903097260633259)
          ·
            refine ⟨4540347311854645890949889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3026898207903097260633259 4540347311854645890949889)
            ·
              refine ⟨3405260483890984418212417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4540347311854645890949889 3405260483890984418212417)
              ·
                refine ⟨2553945362918238313659313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3405260483890984418212417 2553945362918238313659313)
                ·
                  refine ⟨1915459022188678735244485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2553945362918238313659313 1915459022188678735244485)
                  ·
                    refine ⟨359148566660377262858341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915459022188678735244485 359148566660377262858341)
                    ·
                      rfl

theorem cell22_1049159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 2, 2, 2, 4].length) (baseStart_1049159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049159 prefixEnd_1049159 := by exact prefixLift 1049159
  have htrace : WordTrace (prefixWord ++ tailWord_1049159) baseStart_1049159 baseEnd_1049159 := by
    simpa [prefixWord, tailWord_1049159, baseEnd_1049159] using wordTrace_append hprefix tailTrace_1049159
  have hstable : (prefixWord ++ tailWord_1049159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049159).length < 2 ^ (prefixWord ++ tailWord_1049159).sum := by decide
  have hdescent : baseEnd_1049159 < baseStart_1049159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049187 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 6]
def baseStart_1049187 : Nat := 118140960795 + 1049187 * 2 ^ 59
def prefixEnd_1049187 : Nat := 4983230072969 + 3 ^ 40 * 1049187 * 2
def baseEnd_1049187 : Nat := 359158151632594523158255

theorem tailTrace_1049187 : CollatzResearch.WordTrace tailWord_1049187 prefixEnd_1049187 359158151632594523158255 := by
  unfold tailWord_1049187
  simp only [CollatzResearch.WordTrace]
  refine ⟨38266993649982160718913815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25511329099988107145942543 38266993649982160718913815)
  ·
    refine ⟨57400490474973241078370723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38266993649982160718913815 57400490474973241078370723)
    ·
      refine ⟨86100735712459861617556085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57400490474973241078370723 86100735712459861617556085)
      ·
        refine ⟨8071943973043112026645883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86100735712459861617556085 8071943973043112026645883)
        ·
          refine ⟨12107915959564668039968825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8071943973043112026645883 12107915959564668039968825)
          ·
            refine ⟨9080936969673501029976619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12107915959564668039968825 9080936969673501029976619)
            ·
              refine ⟨13621405454510251544964929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080936969673501029976619 13621405454510251544964929)
              ·
                refine ⟨10216054090882688658723697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13621405454510251544964929 10216054090882688658723697)
                ·
                  refine ⟨7662040568162016494042773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10216054090882688658723697 7662040568162016494042773)
                  ·
                    refine ⟨359158151632594523158255, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7662040568162016494042773 359158151632594523158255)
                    ·
                      rfl

theorem cell22_1049187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 6].length) (baseStart_1049187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049187 prefixEnd_1049187 := by exact prefixLift 1049187
  have htrace : WordTrace (prefixWord ++ tailWord_1049187) baseStart_1049187 baseEnd_1049187 := by
    simpa [prefixWord, tailWord_1049187, baseEnd_1049187] using wordTrace_append hprefix tailTrace_1049187
  have hstable : (prefixWord ++ tailWord_1049187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049187).length < 2 ^ (prefixWord ++ tailWord_1049187).sum := by decide
  have hdescent : baseEnd_1049187 < baseStart_1049187 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049219 : List Nat := [1, 1, 1, 3, 3, 1, 5, 2, 5]
def baseStart_1049219 : Nat := 118140960795 + 1049219 * 2 ^ 59
def prefixEnd_1049219 : Nat := 4983230072969 + 3 ^ 40 * 1049219 * 2
def baseEnd_1049219 : Nat := 119723035295519035452719

theorem tailTrace_1049219 : CollatzResearch.WordTrace tailWord_1049219 prefixEnd_1049219 119723035295519035452719 := by
  unfold tailWord_1049219
  simp only [CollatzResearch.WordTrace]
  refine ⟨38268160785866230184078711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25512107190577486789385807 38268160785866230184078711)
  ·
    refine ⟨57402241178799345276118067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38268160785866230184078711 57402241178799345276118067)
    ·
      refine ⟨86103361768199017914177101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57402241178799345276118067 86103361768199017914177101)
      ·
        refine ⟨32288760663074631717816413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86103361768199017914177101 32288760663074631717816413)
        ·
          refine ⟨12108285248652986894181155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32288760663074631717816413 12108285248652986894181155)
          ·
            refine ⟨18162427872979480341271733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12108285248652986894181155 18162427872979480341271733)
            ·
              refine ⟨1702727613091826281994225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18162427872979480341271733 1702727613091826281994225)
              ·
                refine ⟨1277045709818869711495669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702727613091826281994225 1277045709818869711495669)
                ·
                  refine ⟨119723035295519035452719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277045709818869711495669 119723035295519035452719)
                  ·
                    rfl

theorem cell22_1049219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 2, 5].length) (baseStart_1049219 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049219 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049219 prefixEnd_1049219 := by exact prefixLift 1049219
  have htrace : WordTrace (prefixWord ++ tailWord_1049219) baseStart_1049219 baseEnd_1049219 := by
    simpa [prefixWord, tailWord_1049219, baseEnd_1049219] using wordTrace_append hprefix tailTrace_1049219
  have hstable : (prefixWord ++ tailWord_1049219).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049219).length < 2 ^ (prefixWord ++ tailWord_1049219).sum := by decide
  have hdescent : baseEnd_1049219 < baseStart_1049219 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049300 : List Nat := [2, 4, 1, 3, 2, 2, 1, 2, 1, 4]
def baseStart_1049300 : Nat := 118140960795 + 1049300 * 2 ^ 59
def prefixEnd_1049300 : Nat := 4983230072969 + 3 ^ 40 * 1049300 * 2
def baseEnd_1049300 : Nat := 359196833841899895082909

theorem tailTrace_1049300 : CollatzResearch.WordTrace tailWord_1049300 prefixEnd_1049300 359196833841899895082909 := by
  unfold tailWord_1049300
  simp only [CollatzResearch.WordTrace]
  refine ⟨19135557549286390508888677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25514076732381854011851569 19135557549286390508888677)
  ·
    refine ⟨3587917040491198220416627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19135557549286390508888677 3587917040491198220416627)
    ·
      refine ⟨5381875560736797330624941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3587917040491198220416627 5381875560736797330624941)
      ·
        refine ⟨2018203335276298998984353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5381875560736797330624941 2018203335276298998984353)
        ·
          refine ⟨1513652501457224249238265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018203335276298998984353 1513652501457224249238265)
          ·
            refine ⟨1135239376092918186928699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1513652501457224249238265 1135239376092918186928699)
            ·
              refine ⟨1702859064139377280393049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135239376092918186928699 1702859064139377280393049)
              ·
                refine ⟨1277144298104532960294787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1702859064139377280393049 1277144298104532960294787)
                ·
                  refine ⟨1915716447156799440442181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277144298104532960294787 1915716447156799440442181)
                  ·
                    refine ⟨359196833841899895082909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915716447156799440442181 359196833841899895082909)
                    ·
                      rfl

theorem cell22_1049300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 2, 1, 4].length) (baseStart_1049300 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049300 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049300 prefixEnd_1049300 := by exact prefixLift 1049300
  have htrace : WordTrace (prefixWord ++ tailWord_1049300) baseStart_1049300 baseEnd_1049300 := by
    simpa [prefixWord, tailWord_1049300, baseEnd_1049300] using wordTrace_append hprefix tailTrace_1049300
  have hstable : (prefixWord ++ tailWord_1049300).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049300).length < 2 ^ (prefixWord ++ tailWord_1049300).sum := by decide
  have hdescent : baseEnd_1049300 < baseStart_1049300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049311 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 2, 4]
def baseStart_1049311 : Nat := 118140960795 + 1049311 * 2 ^ 59
def prefixEnd_1049311 : Nat := 4983230072969 + 3 ^ 40 * 1049311 * 2
def baseEnd_1049311 : Nat := 359200599366699533057875

theorem tailTrace_1049311 : CollatzResearch.WordTrace tailWord_1049311 prefixEnd_1049311 359200599366699533057875 := by
  unfold tailWord_1049311
  simp only [CollatzResearch.WordTrace]
  refine ⟨38271516301532929896427787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25514344201021953264285191 38271516301532929896427787)
  ·
    refine ⟨57407274452299394844641681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38271516301532929896427787 57407274452299394844641681)
    ·
      refine ⟨43055455839224546133481261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57407274452299394844641681 43055455839224546133481261)
      ·
        refine ⟨16145795939709204800055473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43055455839224546133481261 16145795939709204800055473)
        ·
          refine ⟨12109346954781903600041605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16145795939709204800055473 12109346954781903600041605)
          ·
            refine ⟨2270502554021606925007801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12109346954781903600041605 2270502554021606925007801)
            ·
              refine ⟨1702876915516205193755851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270502554021606925007801 1702876915516205193755851)
              ·
                refine ⟨2554315373274307790633777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702876915516205193755851 2554315373274307790633777)
                ·
                  refine ⟨1915736529955730842975333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554315373274307790633777 1915736529955730842975333)
                  ·
                    refine ⟨359200599366699533057875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915736529955730842975333 359200599366699533057875)
                    ·
                      rfl

theorem cell22_1049311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 4].length) (baseStart_1049311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049311 prefixEnd_1049311 := by exact prefixLift 1049311
  have htrace : WordTrace (prefixWord ++ tailWord_1049311) baseStart_1049311 baseEnd_1049311 := by
    simpa [prefixWord, tailWord_1049311, baseEnd_1049311] using wordTrace_append hprefix tailTrace_1049311
  have hstable : (prefixWord ++ tailWord_1049311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049311).length < 2 ^ (prefixWord ++ tailWord_1049311).sum := by decide
  have hdescent : baseEnd_1049311 < baseStart_1049311 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049332 : List Nat := [2, 6, 1, 1, 2, 1, 1, 4, 4]
def baseStart_1049332 : Nat := 118140960795 + 1049332 * 2 ^ 59
def prefixEnd_1049332 : Nat := 4983230072969 + 3 ^ 40 * 1049332 * 2
def baseEnd_1049332 : Nat := 119735929365287492760937

theorem tailTrace_1049332 : CollatzResearch.WordTrace tailWord_1049332 prefixEnd_1049332 119735929365287492760937 := by
  unfold tailWord_1049332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19136141117228425241471125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25514854822971233655294833 19136141117228425241471125)
  ·
    refine ⟨897006614870082433193959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19136141117228425241471125 897006614870082433193959)
    ·
      refine ⟨1345509922305123649790939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 897006614870082433193959 1345509922305123649790939)
      ·
        refine ⟨2018264883457685474686409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345509922305123649790939 2018264883457685474686409)
        ·
          refine ⟨1513698662593264106014807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018264883457685474686409 1513698662593264106014807)
          ·
            refine ⟨2270547993889896159022211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513698662593264106014807 2270547993889896159022211)
            ·
              refine ⟨3405821990834844238533317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2270547993889896159022211 3405821990834844238533317)
              ·
                refine ⟨638591623281533294724997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3405821990834844238533317 638591623281533294724997)
                ·
                  refine ⟨119735929365287492760937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638591623281533294724997 119735929365287492760937)
                  ·
                    rfl

theorem cell22_1049332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 2, 1, 1, 4, 4].length) (baseStart_1049332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049332 prefixEnd_1049332 := by exact prefixLift 1049332
  have htrace : WordTrace (prefixWord ++ tailWord_1049332) baseStart_1049332 baseEnd_1049332 := by
    simpa [prefixWord, tailWord_1049332, baseEnd_1049332] using wordTrace_append hprefix tailTrace_1049332
  have hstable : (prefixWord ++ tailWord_1049332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049332).length < 2 ^ (prefixWord ++ tailWord_1049332).sum := by decide
  have hdescent : baseEnd_1049332 < baseStart_1049332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049341 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 3, 3]
def baseStart_1049341 : Nat := 118140960795 + 1049341 * 2 ^ 59
def prefixEnd_1049341 : Nat := 4983230072969 + 3 ^ 40 * 1049341 * 2
def baseEnd_1049341 : Nat := 359210868979789454807783

theorem tailTrace_1049341 : CollatzResearch.WordTrace tailWord_1049341 prefixEnd_1049341 359210868979789454807783 := by
  unfold tailWord_1049341
  simp only [CollatzResearch.WordTrace]
  refine ⟨38272610491424245020019877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25515073660949496680013251 38272610491424245020019877)
  ·
    refine ⟨7176114467142045941253727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38272610491424245020019877 7176114467142045941253727)
    ·
      refine ⟨10764171700713068911880591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176114467142045941253727 10764171700713068911880591)
      ·
        refine ⟨16146257551069603367820887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10764171700713068911880591 16146257551069603367820887)
        ·
          refine ⟨24219386326604405051731331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16146257551069603367820887 24219386326604405051731331)
          ·
            refine ⟨36329079489906607577596997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24219386326604405051731331 36329079489906607577596997)
            ·
              refine ⟨6811702404357488920799437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36329079489906607577596997 6811702404357488920799437)
              ·
                refine ⟨2554388401634058345299789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6811702404357488920799437 2554388401634058345299789)
                ·
                  refine ⟨957895650612771879487421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2554388401634058345299789 957895650612771879487421)
                  ·
                    refine ⟨359210868979789454807783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957895650612771879487421 359210868979789454807783)
                    ·
                      rfl

theorem cell22_1049341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 3].length) (baseStart_1049341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049341 prefixEnd_1049341 := by exact prefixLift 1049341
  have htrace : WordTrace (prefixWord ++ tailWord_1049341) baseStart_1049341 baseEnd_1049341 := by
    simpa [prefixWord, tailWord_1049341, baseEnd_1049341] using wordTrace_append hprefix tailTrace_1049341
  have hstable : (prefixWord ++ tailWord_1049341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049341).length < 2 ^ (prefixWord ++ tailWord_1049341).sum := by decide
  have hdescent : baseEnd_1049341 < baseStart_1049341 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049362 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 2, 4]
def baseStart_1049362 : Nat := 118140960795 + 1049362 * 2 ^ 59
def prefixEnd_1049362 : Nat := 4983230072969 + 3 ^ 40 * 1049362 * 2
def baseEnd_1049362 : Nat := 359218057708952400032719

theorem tailTrace_1049362 : CollatzResearch.WordTrace tailWord_1049362 prefixEnd_1049362 359218057708952400032719 := by
  unfold tailWord_1049362
  simp only [CollatzResearch.WordTrace]
  refine ⟨9568344106087041401633585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25515584282898777071022893 9568344106087041401633585)
  ·
    refine ⟨7176258079565281051225189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9568344106087041401633585 7176258079565281051225189)
    ·
      refine ⟨1345548389918490197104723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7176258079565281051225189 1345548389918490197104723)
      ·
        refine ⟨2018322584877735295657085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1345548389918490197104723 2018322584877735295657085)
        ·
          refine ⟨756870969329150735871407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2018322584877735295657085 756870969329150735871407)
          ·
            refine ⟨1135306453993726103807111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 756870969329150735871407 1135306453993726103807111)
            ·
              refine ⟨1702959680990589155710667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135306453993726103807111 1702959680990589155710667)
              ·
                refine ⟨2554439521485883733566001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1702959680990589155710667 2554439521485883733566001)
                ·
                  refine ⟨1915829641114412800174501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2554439521485883733566001 1915829641114412800174501)
                  ·
                    refine ⟨359218057708952400032719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1915829641114412800174501 359218057708952400032719)
                    ·
                      rfl

theorem cell22_1049362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 4].length) (baseStart_1049362 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049362 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049362 prefixEnd_1049362 := by exact prefixLift 1049362
  have htrace : WordTrace (prefixWord ++ tailWord_1049362) baseStart_1049362 baseEnd_1049362 := by
    simpa [prefixWord, tailWord_1049362, baseEnd_1049362] using wordTrace_append hprefix tailTrace_1049362
  have hstable : (prefixWord ++ tailWord_1049362).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049362).length < 2 ^ (prefixWord ++ tailWord_1049362).sum := by decide
  have hdescent : baseEnd_1049362 < baseStart_1049362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049375 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 1, 3]
def baseStart_1049375 : Nat := 118140960795 + 1049375 * 2 ^ 59
def prefixEnd_1049375 : Nat := 4983230072969 + 3 ^ 40 * 1049375 * 2
def baseEnd_1049375 : Nat := 359222507874624699457679

theorem tailTrace_1049375 : CollatzResearch.WordTrace tailWord_1049375 prefixEnd_1049375 359222507874624699457679 := by
  unfold tailWord_1049375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38273850573301068826757579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25515900382200712551171719 38273850573301068826757579)
  ·
    refine ⟨57410775859951603240136369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38273850573301068826757579 57410775859951603240136369)
    ·
      refine ⟨43058081894963702430102277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57410775859951603240136369 43058081894963702430102277)
      ·
        refine ⟨8073390355305694205644177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43058081894963702430102277 8073390355305694205644177)
        ·
          refine ⟨6055042766479270654233133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8073390355305694205644177 6055042766479270654233133)
          ·
            refine ⟨2270641037429726495337425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6055042766479270654233133 2270641037429726495337425)
            ·
              refine ⟨1702980778072294871503069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2270641037429726495337425 1702980778072294871503069)
              ·
                refine ⟨638617791777110576813651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1702980778072294871503069 638617791777110576813651)
                ·
                  refine ⟨957926687665665865220477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 638617791777110576813651 957926687665665865220477)
                  ·
                    refine ⟨359222507874624699457679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957926687665665865220477 359222507874624699457679)
                    ·
                      rfl

theorem cell22_1049375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 3].length) (baseStart_1049375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049375 prefixEnd_1049375 := by exact prefixLift 1049375
  have htrace : WordTrace (prefixWord ++ tailWord_1049375) baseStart_1049375 baseEnd_1049375 := by
    simpa [prefixWord, tailWord_1049375, baseEnd_1049375] using wordTrace_append hprefix tailTrace_1049375
  have hstable : (prefixWord ++ tailWord_1049375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049375).length < 2 ^ (prefixWord ++ tailWord_1049375).sum := by decide
  have hdescent : baseEnd_1049375 < baseStart_1049375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049405 : List Nat := [1, 4, 1, 4, 2, 1, 3, 1, 5]
def baseStart_1049405 : Nat := 118140960795 + 1049405 * 2 ^ 59
def prefixEnd_1049405 : Nat := 4983230072969 + 3 ^ 40 * 1049405 * 2
def baseEnd_1049405 : Nat := 119744259162571540402529

theorem tailTrace_1049405 : CollatzResearch.WordTrace tailWord_1049405 prefixEnd_1049405 119744259162571540402529 := by
  unfold tailWord_1049405
  simp only [CollatzResearch.WordTrace]
  refine ⟨38274944763192383950349669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25516629842128255966899779 38274944763192383950349669)
  ·
    refine ⟨7176552143098571990690563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38274944763192383950349669 7176552143098571990690563)
    ·
      refine ⟨10764828214647857986035845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7176552143098571990690563 10764828214647857986035845)
      ·
        refine ⟨2018405290246473372381721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10764828214647857986035845 2018405290246473372381721)
        ·
          refine ⟨1513803967684855029286291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2018405290246473372381721 1513803967684855029286291)
          ·
            refine ⟨2270705951527282543929437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1513803967684855029286291 2270705951527282543929437)
            ·
              refine ⟨851514731822730953973539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2270705951527282543929437 851514731822730953973539)
              ·
                refine ⟨1277272097734096430960309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851514731822730953973539 1277272097734096430960309)
                ·
                  refine ⟨119744259162571540402529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277272097734096430960309 119744259162571540402529)
                  ·
                    rfl

theorem cell22_1049405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3, 1, 5].length) (baseStart_1049405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049405 prefixEnd_1049405 := by exact prefixLift 1049405
  have htrace : WordTrace (prefixWord ++ tailWord_1049405) baseStart_1049405 baseEnd_1049405 := by
    simpa [prefixWord, tailWord_1049405, baseEnd_1049405] using wordTrace_append hprefix tailTrace_1049405
  have hstable : (prefixWord ++ tailWord_1049405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049405).length < 2 ^ (prefixWord ++ tailWord_1049405).sum := by decide
  have hdescent : baseEnd_1049405 < baseStart_1049405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049433 : List Nat := [1, 2, 1, 2, 2, 4, 3, 3, 4]
def baseStart_1049433 : Nat := 118140960795 + 1049433 * 2 ^ 59
def prefixEnd_1049433 : Nat := 4983230072969 + 3 ^ 40 * 1049433 * 2
def baseEnd_1049433 : Nat := 119747454153310627169167

theorem tailTrace_1049433 : CollatzResearch.WordTrace tailWord_1049433 prefixEnd_1049433 119747454153310627169167 := by
  unfold tailWord_1049433
  simp only [CollatzResearch.WordTrace]
  refine ⟨38275966007090944732368953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25517310671393963154912635 38275966007090944732368953)
  ·
    refine ⟨28706974505318208549276715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38275966007090944732368953 28706974505318208549276715)
    ·
      refine ⟨43060461757977312823915073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28706974505318208549276715 43060461757977312823915073)
      ·
        refine ⟨32295346318482984617936305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43060461757977312823915073 32295346318482984617936305)
        ·
          refine ⟨24221509738862238463452229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32295346318482984617936305 24221509738862238463452229)
          ·
            refine ⟨4541533076036669711897293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24221509738862238463452229 4541533076036669711897293)
            ·
              refine ⟨1703074903513751141961485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4541533076036669711897293 1703074903513751141961485)
              ·
                refine ⟨638653088817656678235557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1703074903513751141961485 638653088817656678235557)
                ·
                  refine ⟨119747454153310627169167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638653088817656678235557 119747454153310627169167)
                  ·
                    rfl

theorem cell22_1049433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 3, 3, 4].length) (baseStart_1049433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049433 prefixEnd_1049433 := by exact prefixLift 1049433
  have htrace : WordTrace (prefixWord ++ tailWord_1049433) baseStart_1049433 baseEnd_1049433 := by
    simpa [prefixWord, tailWord_1049433, baseEnd_1049433] using wordTrace_append hprefix tailTrace_1049433
  have hstable : (prefixWord ++ tailWord_1049433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049433).length < 2 ^ (prefixWord ++ tailWord_1049433).sum := by decide
  have hdescent : baseEnd_1049433 < baseStart_1049433 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049448 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 4, 3]
def baseStart_1049448 : Nat := 118140960795 + 1049448 * 2 ^ 59
def prefixEnd_1049448 : Nat := 4983230072969 + 3 ^ 40 * 1049448 * 2
def baseEnd_1049448 : Nat := 359247497266476842382455

theorem tailTrace_1049448 : CollatzResearch.WordTrace tailWord_1049448 prefixEnd_1049448 359247497266476842382455 := by
  unfold tailWord_1049448
  simp only [CollatzResearch.WordTrace]
  refine ⟨19138256551018301147082499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25517675401357734862776665 19138256551018301147082499)
  ·
    refine ⟨28707384826527451720623749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19138256551018301147082499 28707384826527451720623749)
    ·
      refine ⟨5382634654973897197616953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28707384826527451720623749 5382634654973897197616953)
      ·
        refine ⟨4036975991230422898212715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5382634654973897197616953 4036975991230422898212715)
        ·
          refine ⟨6055463986845634347319073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4036975991230422898212715 6055463986845634347319073)
          ·
            refine ⟨4541597990134225760489305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6055463986845634347319073 4541597990134225760489305)
            ·
              refine ⟨3406198492600669320366979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4541597990134225760489305 3406198492600669320366979)
              ·
                refine ⟨5109297738901003980550469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3406198492600669320366979 5109297738901003980550469)
                ·
                  refine ⟨957993326043938246353213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5109297738901003980550469 957993326043938246353213)
                  ·
                    refine ⟨359247497266476842382455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 957993326043938246353213 359247497266476842382455)
                    ·
                      rfl

theorem cell22_1049448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 3].length) (baseStart_1049448 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049448 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049448 prefixEnd_1049448 := by exact prefixLift 1049448
  have htrace : WordTrace (prefixWord ++ tailWord_1049448) baseStart_1049448 baseEnd_1049448 := by
    simpa [prefixWord, tailWord_1049448, baseEnd_1049448] using wordTrace_append hprefix tailTrace_1049448
  have hstable : (prefixWord ++ tailWord_1049448).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049448).length < 2 ^ (prefixWord ++ tailWord_1049448).sum := by decide
  have hdescent : baseEnd_1049448 < baseStart_1049448 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049461 : List Nat := [1, 3, 4, 1, 1, 2, 1, 9]
def baseStart_1049461 : Nat := 118140960795 + 1049461 * 2 ^ 59
def prefixEnd_1049461 : Nat := 4983230072969 + 3 ^ 40 * 1049461 * 2
def baseEnd_1049461 : Nat := 39916883048016571311935

theorem tailTrace_1049461 : CollatzResearch.WordTrace tailWord_1049461 prefixEnd_1049461 39916883048016571311935 := by
  unfold tailWord_1049461
  simp only [CollatzResearch.WordTrace]
  refine ⟨38276987250989505514388237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25517991500659670342925491 38276987250989505514388237)
  ·
    refine ⟨14353870219121064567895589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38276987250989505514388237 14353870219121064567895589)
    ·
      refine ⟨2691350666085199606480423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14353870219121064567895589 2691350666085199606480423)
      ·
        refine ⟨4037025999127799409720635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2691350666085199606480423 4037025999127799409720635)
        ·
          refine ⟨6055538998691699114580953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4037025999127799409720635 6055538998691699114580953)
          ·
            refine ⟨4541654249018774335935715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6055538998691699114580953 4541654249018774335935715)
            ·
              refine ⟨6812481373528161503903573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4541654249018774335935715 6812481373528161503903573)
              ·
                refine ⟨39916883048016571311935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6812481373528161503903573 39916883048016571311935)
                ·
                  rfl

theorem cell22_1049461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 9].length) (baseStart_1049461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049461 prefixEnd_1049461 := by exact prefixLift 1049461
  have htrace : WordTrace (prefixWord ++ tailWord_1049461) baseStart_1049461 baseEnd_1049461 := by
    simpa [prefixWord, tailWord_1049461, baseEnd_1049461] using wordTrace_append hprefix tailTrace_1049461
  have hstable : (prefixWord ++ tailWord_1049461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049461).length < 2 ^ (prefixWord ++ tailWord_1049461).sum := by decide
  have hdescent : baseEnd_1049461 < baseStart_1049461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049465 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 2, 3]
def baseStart_1049465 : Nat := 118140960795 + 1049465 * 2 ^ 59
def prefixEnd_1049465 : Nat := 4983230072969 + 3 ^ 40 * 1049465 * 2
def baseEnd_1049465 : Nat := 359253316713894464707403

theorem tailTrace_1049465 : CollatzResearch.WordTrace tailWord_1049465 prefixEnd_1049465 359253316713894464707403 := by
  unfold tailWord_1049465
  simp only [CollatzResearch.WordTrace]
  refine ⟨38277133142975014197533849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25518088761983342798355899 38277133142975014197533849)
  ·
    refine ⟨28707849857231260648150387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38277133142975014197533849 28707849857231260648150387)
    ·
      refine ⟨43061774785846890972225581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28707849857231260648150387 43061774785846890972225581)
      ·
        refine ⟨16148165544692584114584593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43061774785846890972225581 16148165544692584114584593)
        ·
          refine ⟨12111124158519438085938445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16148165544692584114584593 12111124158519438085938445)
          ·
            refine ⟨4541671559444789282226917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12111124158519438085938445 4541671559444789282226917)
            ·
              refine ⟨851563417395897990417547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4541671559444789282226917 851563417395897990417547)
              ·
                refine ⟨1277345126093846985626321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851563417395897990417547 1277345126093846985626321)
                ·
                  refine ⟨958008844570385239219741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277345126093846985626321 958008844570385239219741)
                  ·
                    refine ⟨359253316713894464707403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958008844570385239219741 359253316713894464707403)
                    ·
                      rfl

theorem cell22_1049465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 3].length) (baseStart_1049465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049465 prefixEnd_1049465 := by exact prefixLift 1049465
  have htrace : WordTrace (prefixWord ++ tailWord_1049465) baseStart_1049465 baseEnd_1049465 := by
    simpa [prefixWord, tailWord_1049465, baseEnd_1049465] using wordTrace_append hprefix tailTrace_1049465
  have hstable : (prefixWord ++ tailWord_1049465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049465).length < 2 ^ (prefixWord ++ tailWord_1049465).sum := by decide
  have hdescent : baseEnd_1049465 < baseStart_1049465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049553 : List Nat := [1, 2, 2, 1, 2, 1, 5, 3, 1, 4]
def baseStart_1049553 : Nat := 118140960795 + 1049553 * 2 ^ 59
def prefixEnd_1049553 : Nat := 4983230072969 + 3 ^ 40 * 1049553 * 2
def baseEnd_1049553 : Nat := 359283440912291568507133

theorem tailTrace_1049553 : CollatzResearch.WordTrace tailWord_1049553 prefixEnd_1049553 359283440912291568507133 := by
  unfold tailWord_1049553
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280342766656205226737313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520228511104136817824875 38280342766656205226737313)
  ·
    refine ⟨28710257074992153920052985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38280342766656205226737313 28710257074992153920052985)
    ·
      refine ⟨21532692806244115440039739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28710257074992153920052985 21532692806244115440039739)
      ·
        refine ⟨32299039209366173160059609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21532692806244115440039739 32299039209366173160059609)
        ·
          refine ⟨24224279407024629870044707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32299039209366173160059609 24224279407024629870044707)
          ·
            refine ⟨36336419110536944805067061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24224279407024629870044707 36336419110536944805067061)
            ·
              refine ⟨3406539291612838575475037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36336419110536944805067061 3406539291612838575475037)
              ·
                refine ⟨1277452234354814465803139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3406539291612838575475037 1277452234354814465803139)
                ·
                  refine ⟨1916178351532221698704709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1277452234354814465803139 1916178351532221698704709)
                  ·
                    refine ⟨359283440912291568507133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916178351532221698704709 359283440912291568507133)
                    ·
                      rfl

theorem cell22_1049553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 3, 1, 4].length) (baseStart_1049553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049553 prefixEnd_1049553 := by exact prefixLift 1049553
  have htrace : WordTrace (prefixWord ++ tailWord_1049553) baseStart_1049553 baseEnd_1049553 := by
    simpa [prefixWord, tailWord_1049553, baseEnd_1049553] using wordTrace_append hprefix tailTrace_1049553
  have hstable : (prefixWord ++ tailWord_1049553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049553).length < 2 ^ (prefixWord ++ tailWord_1049553).sum := by decide
  have hdescent : baseEnd_1049553 < baseStart_1049553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049557 : List Nat := [1, 3, 2, 3, 4, 1, 1, 2, 5]
def baseStart_1049557 : Nat := 118140960795 + 1049557 * 2 ^ 59
def prefixEnd_1049557 : Nat := 4983230072969 + 3 ^ 40 * 1049557 * 2
def baseEnd_1049557 : Nat := 119761603398012297135707

theorem tailTrace_1049557 : CollatzResearch.WordTrace tailWord_1049557 prefixEnd_1049557 119761603398012297135707 := by
  unfold tailWord_1049557
  simp only [CollatzResearch.WordTrace]
  refine ⟨38280488658641713909882925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520325772427809273255283 38280488658641713909882925)
  ·
    refine ⟨14355183246990642716206097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38280488658641713909882925 14355183246990642716206097)
    ·
      refine ⟨10766387435242982037154573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14355183246990642716206097 10766387435242982037154573)
      ·
        refine ⟨4037395288216118263932965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10766387435242982037154573 4037395288216118263932965)
        ·
          refine ⟨757011616540522174487431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4037395288216118263932965 757011616540522174487431)
          ·
            refine ⟨1135517424810783261731147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 757011616540522174487431 1135517424810783261731147)
            ·
              refine ⟨1703276137216174892596721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135517424810783261731147 1703276137216174892596721)
              ·
                refine ⟨1277457102912131169447541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1703276137216174892596721 1277457102912131169447541)
                ·
                  refine ⟨119761603398012297135707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1277457102912131169447541 119761603398012297135707)
                  ·
                    rfl

theorem cell22_1049557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 2, 5].length) (baseStart_1049557 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049557 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049557 prefixEnd_1049557 := by exact prefixLift 1049557
  have htrace : WordTrace (prefixWord ++ tailWord_1049557) baseStart_1049557 baseEnd_1049557 := by
    simpa [prefixWord, tailWord_1049557, baseEnd_1049557] using wordTrace_append hprefix tailTrace_1049557
  have hstable : (prefixWord ++ tailWord_1049557).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049557).length < 2 ^ (prefixWord ++ tailWord_1049557).sum := by decide
  have hdescent : baseEnd_1049557 < baseStart_1049557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049583 : List Nat := [1, 1, 2, 1, 4, 3, 3, 1, 1, 5]
def baseStart_1049583 : Nat := 118140960795 + 1049583 * 2 ^ 59
def prefixEnd_1049583 : Nat := 4983230072969 + 3 ^ 40 * 1049583 * 2
def baseEnd_1049583 : Nat := 359293710525381490257041

theorem tailTrace_1049583 : CollatzResearch.WordTrace tailWord_1049583 prefixEnd_1049583 359293710525381490257041 := by
  unfold tailWord_1049583
  simp only [CollatzResearch.WordTrace]
  refine ⟨38281436956547520350329403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25520957971031680233552935 38281436956547520350329403)
  ·
    refine ⟨57422155434821280525494105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38281436956547520350329403 57422155434821280525494105)
    ·
      refine ⟨43066616576115960394120579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57422155434821280525494105 43066616576115960394120579)
      ·
        refine ⟨64599924864173940591180869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43066616576115960394120579 64599924864173940591180869)
        ·
          refine ⟨12112485912032613860846413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64599924864173940591180869 12112485912032613860846413)
          ·
            refine ⟨4542182217012230197817405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12112485912032613860846413 4542182217012230197817405)
            ·
              refine ⟨1703318331379586324181527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4542182217012230197817405 1703318331379586324181527)
              ·
                refine ⟨2554977497069379486272291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703318331379586324181527 2554977497069379486272291)
                ·
                  refine ⟨3832466245604069229408437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2554977497069379486272291 3832466245604069229408437)
                  ·
                    refine ⟨359293710525381490257041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3832466245604069229408437 359293710525381490257041)
                    ·
                      rfl

theorem cell22_1049583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 3, 1, 1, 5].length) (baseStart_1049583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049583 prefixEnd_1049583 := by exact prefixLift 1049583
  have htrace : WordTrace (prefixWord ++ tailWord_1049583) baseStart_1049583 baseEnd_1049583 := by
    simpa [prefixWord, tailWord_1049583, baseEnd_1049583] using wordTrace_append hprefix tailTrace_1049583
  have hstable : (prefixWord ++ tailWord_1049583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049583).length < 2 ^ (prefixWord ++ tailWord_1049583).sum := by decide
  have hdescent : baseEnd_1049583 < baseStart_1049583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049634 : List Nat := [3, 3, 1, 1, 1, 5, 2, 1, 2, 3]
def baseStart_1049634 : Nat := 118140960795 + 1049634 * 2 ^ 59
def prefixEnd_1049634 : Nat := 4983230072969 + 3 ^ 40 * 1049634 * 2
def baseEnd_1049634 : Nat := 359311168867634357231885

theorem tailTrace_1049634 : CollatzResearch.WordTrace tailWord_1049634 prefixEnd_1049634 359311168867634357231885 := by
  unfold tailWord_1049634
  simp only [CollatzResearch.WordTrace]
  refine ⟨9570824269840689015108989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25522198052908504040290637 9570824269840689015108989)
  ·
    refine ⟨3589059101190258380665871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9570824269840689015108989 3589059101190258380665871)
    ·
      refine ⟨5383588651785387570998807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3589059101190258380665871 5383588651785387570998807)
      ·
        refine ⟨8075382977678081356498211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383588651785387570998807 8075382977678081356498211)
        ·
          refine ⟨12113074466517122034747317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8075382977678081356498211 12113074466517122034747317)
          ·
            refine ⟨1135600731235980190757561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12113074466517122034747317 1135600731235980190757561)
            ·
              refine ⟨851700548426985143068171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1135600731235980190757561 851700548426985143068171)
              ·
                refine ⟨1277550822640477714602257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 851700548426985143068171 1277550822640477714602257)
                ·
                  refine ⟨958163116980358285951693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1277550822640477714602257 958163116980358285951693)
                  ·
                    refine ⟨359311168867634357231885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958163116980358285951693 359311168867634357231885)
                    ·
                      rfl

theorem cell22_1049634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_1049634 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049634 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049634 prefixEnd_1049634 := by exact prefixLift 1049634
  have htrace : WordTrace (prefixWord ++ tailWord_1049634) baseStart_1049634 baseEnd_1049634 := by
    simpa [prefixWord, tailWord_1049634, baseEnd_1049634] using wordTrace_append hprefix tailTrace_1049634
  have hstable : (prefixWord ++ tailWord_1049634).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049634).length < 2 ^ (prefixWord ++ tailWord_1049634).sum := by decide
  have hdescent : baseEnd_1049634 < baseStart_1049634 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049688 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 5, 4]
def baseStart_1049688 : Nat := 118140960795 + 1049688 * 2 ^ 59
def prefixEnd_1049688 : Nat := 4983230072969 + 3 ^ 40 * 1049688 * 2
def baseEnd_1049688 : Nat := 359329654171196216381719

theorem tailTrace_1049688 : CollatzResearch.WordTrace tailWord_1049688 prefixEnd_1049688 359329654171196216381719 := by
  unfold tailWord_1049688
  simp only [CollatzResearch.WordTrace]
  refine ⟨19142633310583561641450859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25523511080778082188601145 19142633310583561641450859)
  ·
    refine ⟨28713949965875342462176289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19142633310583561641450859 28713949965875342462176289)
    ·
      refine ⟨21535462474406506846632217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28713949965875342462176289 21535462474406506846632217)
      ·
        refine ⟨16151596855804880134974163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21535462474406506846632217 16151596855804880134974163)
        ·
          refine ⟨24227395283707320202461245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16151596855804880134974163 24227395283707320202461245)
          ·
            refine ⟨9085273231390245075922967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24227395283707320202461245 9085273231390245075922967)
            ·
              refine ⟨13627909847085367613884451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9085273231390245075922967 13627909847085367613884451)
              ·
                refine ⟨20441864770628051420826677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13627909847085367613884451 20441864770628051420826677)
                ·
                  refine ⟨1916424822246379820702501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 20441864770628051420826677 1916424822246379820702501)
                  ·
                    refine ⟨359329654171196216381719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1916424822246379820702501 359329654171196216381719)
                    ·
                      rfl

theorem cell22_1049688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 4].length) (baseStart_1049688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049688 prefixEnd_1049688 := by exact prefixLift 1049688
  have htrace : WordTrace (prefixWord ++ tailWord_1049688) baseStart_1049688 baseEnd_1049688 := by
    simpa [prefixWord, tailWord_1049688, baseEnd_1049688] using wordTrace_append hprefix tailTrace_1049688
  have hstable : (prefixWord ++ tailWord_1049688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049688).length < 2 ^ (prefixWord ++ tailWord_1049688).sum := by decide
  have hdescent : baseEnd_1049688 < baseStart_1049688 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049703 : List Nat := [1, 1, 5, 1, 1, 3, 1, 1, 8]
def baseStart_1049703 : Nat := 118140960795 + 1049703 * 2 ^ 59
def prefixEnd_1049703 : Nat := 4983230072969 + 3 ^ 40 * 1049703 * 2
def baseEnd_1049703 : Nat := 119778262992580392418891

theorem tailTrace_1049703 : CollatzResearch.WordTrace tailWord_1049703 prefixEnd_1049703 119778262992580392418891 := by
  unfold tailWord_1049703
  simp only [CollatzResearch.WordTrace]
  refine ⟨38285813716112780844697763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25523875810741853896465175 38285813716112780844697763)
  ·
    refine ⟨57428720574169171267046645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38285813716112780844697763 57428720574169171267046645)
    ·
      refine ⟨5383942553828359806285623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57428720574169171267046645 5383942553828359806285623)
      ·
        refine ⟨8075913830742539709428435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5383942553828359806285623 8075913830742539709428435)
        ·
          refine ⟨12113870746113809564142653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8075913830742539709428435 12113870746113809564142653)
          ·
            refine ⟨4542701529792678586553495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12113870746113809564142653 4542701529792678586553495)
            ·
              refine ⟨6814052294689017879830243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4542701529792678586553495 6814052294689017879830243)
              ·
                refine ⟨10221078442033526819745365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6814052294689017879830243 10221078442033526819745365)
                ·
                  refine ⟨119778262992580392418891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10221078442033526819745365 119778262992580392418891)
                  ·
                    rfl

theorem cell22_1049703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 1, 8].length) (baseStart_1049703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049703 prefixEnd_1049703 := by exact prefixLift 1049703
  have htrace : WordTrace (prefixWord ++ tailWord_1049703) baseStart_1049703 baseEnd_1049703 := by
    simpa [prefixWord, tailWord_1049703, baseEnd_1049703] using wordTrace_append hprefix tailTrace_1049703
  have hstable : (prefixWord ++ tailWord_1049703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049703).length < 2 ^ (prefixWord ++ tailWord_1049703).sum := by decide
  have hdescent : baseEnd_1049703 < baseStart_1049703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049720 : List Nat := [2, 1, 2, 1, 1, 1, 5, 5, 4]
def baseStart_1049720 : Nat := 118140960795 + 1049720 * 2 ^ 59
def prefixEnd_1049720 : Nat := 4983230072969 + 3 ^ 40 * 1049720 * 2
def baseEnd_1049720 : Nat := 119780202808386266527207

theorem tailTrace_1049720 : CollatzResearch.WordTrace tailWord_1049720 prefixEnd_1049720 119780202808386266527207 := by
  unfold tailWord_1049720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19143216878525596374033307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25524289171367461832044409 19143216878525596374033307)
  ·
    refine ⟨28714825317788394561049961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19143216878525596374033307 28714825317788394561049961)
    ·
      refine ⟨21536118988341295920787471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28714825317788394561049961 21536118988341295920787471)
      ·
        refine ⟨32304178482511943881181207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21536118988341295920787471 32304178482511943881181207)
        ·
          refine ⟨48456267723767915821771811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32304178482511943881181207 48456267723767915821771811)
          ·
            refine ⟨72684401585651873732657717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48456267723767915821771811 72684401585651873732657717)
            ·
              refine ⟨6814162648654863162436661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72684401585651873732657717 6814162648654863162436661)
              ·
                refine ⟨638827748311393421478437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6814162648654863162436661 638827748311393421478437)
                ·
                  refine ⟨119780202808386266527207, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 638827748311393421478437 119780202808386266527207)
                  ·
                    rfl

theorem cell22_1049720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 5, 5, 4].length) (baseStart_1049720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049720 prefixEnd_1049720 := by exact prefixLift 1049720
  have htrace : WordTrace (prefixWord ++ tailWord_1049720) baseStart_1049720 baseEnd_1049720 := by
    simpa [prefixWord, tailWord_1049720, baseEnd_1049720] using wordTrace_append hprefix tailTrace_1049720
  have hstable : (prefixWord ++ tailWord_1049720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049720).length < 2 ^ (prefixWord ++ tailWord_1049720).sum := by decide
  have hdescent : baseEnd_1049720 < baseStart_1049720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049752 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 1, 5]
def baseStart_1049752 : Nat := 118140960795 + 1049752 * 2 ^ 59
def prefixEnd_1049752 : Nat := 4983230072969 + 3 ^ 40 * 1049752 * 2
def baseEnd_1049752 : Nat := 359351562679121382781523

theorem tailTrace_1049752 : CollatzResearch.WordTrace tailWord_1049752 prefixEnd_1049752 359351562679121382781523 := by
  unfold tailWord_1049752
  simp only [CollatzResearch.WordTrace]
  refine ⟨19143800446467631106615755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25525067261956841475487673 19143800446467631106615755)
  ·
    refine ⟨28715700669701446659923633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19143800446467631106615755 28715700669701446659923633)
    ·
      refine ⟨21536775502276084994942725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28715700669701446659923633 21536775502276084994942725)
      ·
        refine ⟨4038145406676765936551761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21536775502276084994942725 4038145406676765936551761)
        ·
          refine ⟨3028609055007574452413821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4038145406676765936551761 3028609055007574452413821)
          ·
            refine ⟨1135728395627840419655183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3028609055007574452413821 1135728395627840419655183)
            ·
              refine ⟨1703592593441760629482775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1135728395627840419655183 1703592593441760629482775)
              ·
                refine ⟨2555388890162640944224163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1703592593441760629482775 2555388890162640944224163)
                ·
                  refine ⟨3833083335243961416336245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2555388890162640944224163 3833083335243961416336245)
                  ·
                    refine ⟨359351562679121382781523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3833083335243961416336245 359351562679121382781523)
                    ·
                      rfl

theorem cell22_1049752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 5].length) (baseStart_1049752 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049752 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049752 prefixEnd_1049752 := by exact prefixLift 1049752
  have htrace : WordTrace (prefixWord ++ tailWord_1049752) baseStart_1049752 baseEnd_1049752 := by
    simpa [prefixWord, tailWord_1049752, baseEnd_1049752] using wordTrace_append hprefix tailTrace_1049752
  have hstable : (prefixWord ++ tailWord_1049752).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049752).length < 2 ^ (prefixWord ++ tailWord_1049752).sum := by decide
  have hdescent : baseEnd_1049752 < baseStart_1049752 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049765 : List Nat := [1, 3, 1, 2, 1, 4, 4, 6]
def baseStart_1049765 : Nat := 118140960795 + 1049765 * 2 ^ 59
def prefixEnd_1049765 : Nat := 4983230072969 + 3 ^ 40 * 1049765 * 2
def baseEnd_1049765 : Nat := 39928445871643742467387

theorem tailTrace_1049765 : CollatzResearch.WordTrace tailWord_1049765 prefixEnd_1049765 39928445871643742467387 := by
  unfold tailWord_1049765
  simp only [CollatzResearch.WordTrace]
  refine ⟨38288075041888165433454749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25525383361258776955636499 38288075041888165433454749)
  ·
    refine ⟨14358028140708062037545531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38288075041888165433454749 14358028140708062037545531)
    ·
      refine ⟨21537042211062093056318297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14358028140708062037545531 21537042211062093056318297)
      ·
        refine ⟨16152781658296569792238723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21537042211062093056318297 16152781658296569792238723)
        ·
          refine ⟨24229172487444854688358085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16152781658296569792238723 24229172487444854688358085)
          ·
            refine ⟨4542969841395910254067141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24229172487444854688358085 4542969841395910254067141)
            ·
              refine ⟨851806845261733172637589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4542969841395910254067141 851806845261733172637589)
              ·
                refine ⟨39928445871643742467387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 851806845261733172637589 39928445871643742467387)
                ·
                  rfl

theorem cell22_1049765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 4, 6].length) (baseStart_1049765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049765 prefixEnd_1049765 := by exact prefixLift 1049765
  have htrace : WordTrace (prefixWord ++ tailWord_1049765) baseStart_1049765 baseEnd_1049765 := by
    simpa [prefixWord, tailWord_1049765, baseEnd_1049765] using wordTrace_append hprefix tailTrace_1049765
  have hstable : (prefixWord ++ tailWord_1049765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049765).length < 2 ^ (prefixWord ++ tailWord_1049765).sum := by decide
  have hdescent : baseEnd_1049765 < baseStart_1049765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049930 : List Nat := [3, 1, 2, 1, 1, 1, 1, 4, 2, 6]
def baseStart_1049930 : Nat := 118140960795 + 1049930 * 2 ^ 59
def prefixEnd_1049930 : Nat := 4983230072969 + 3 ^ 40 * 1049930 * 2
def baseEnd_1049930 : Nat := 359412495716788251830977

theorem tailTrace_1049930 : CollatzResearch.WordTrace tailWord_1049930 prefixEnd_1049930 359412495716788251830977 := by
  unfold tailWord_1049930
  simp only [CollatzResearch.WordTrace]
  refine ⟨9573523271572599653302811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25529395390860265742140829 9573523271572599653302811)
  ·
    refine ⟨14360284907358899479954217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9573523271572599653302811 14360284907358899479954217)
    ·
      refine ⟨10770213680519174609965663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14360284907358899479954217 10770213680519174609965663)
      ·
        refine ⟨16155320520778761914948495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10770213680519174609965663 16155320520778761914948495)
        ·
          refine ⟨24232980781168142872422743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16155320520778761914948495 24232980781168142872422743)
          ·
            refine ⟨36349471171752214308634115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24232980781168142872422743 36349471171752214308634115)
            ·
              refine ⟨54524206757628321462951173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36349471171752214308634115 54524206757628321462951173)
              ·
                refine ⟨10223288767055310274303345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54524206757628321462951173 10223288767055310274303345)
                ·
                  refine ⟨7667466575291482705727509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10223288767055310274303345 7667466575291482705727509)
                  ·
                    refine ⟨359412495716788251830977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7667466575291482705727509 359412495716788251830977)
                    ·
                      rfl

theorem cell22_1049930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 1, 4, 2, 6].length) (baseStart_1049930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049930 prefixEnd_1049930 := by exact prefixLift 1049930
  have htrace : WordTrace (prefixWord ++ tailWord_1049930) baseStart_1049930 baseEnd_1049930 := by
    simpa [prefixWord, tailWord_1049930, baseEnd_1049930] using wordTrace_append hprefix tailTrace_1049930
  have hstable : (prefixWord ++ tailWord_1049930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049930).length < 2 ^ (prefixWord ++ tailWord_1049930).sum := by decide
  have hdescent : baseEnd_1049930 < baseStart_1049930 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1049945 : List Nat := [1, 2, 1, 2, 2, 2, 3, 2, 7]
def baseStart_1049945 : Nat := 118140960795 + 1049945 * 2 ^ 59
def prefixEnd_1049945 : Nat := 4983230072969 + 3 ^ 40 * 1049945 * 2
def baseEnd_1049945 : Nat := 119805876841111070901977

theorem tailTrace_1049945 : CollatzResearch.WordTrace tailWord_1049945 prefixEnd_1049945 119805876841111070901977 := by
  unfold tailWord_1049945
  simp only [CollatzResearch.WordTrace]
  refine ⟨38294640181236056175007289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25529760120824037450004859 38294640181236056175007289)
  ·
    refine ⟨28720980135927042131255467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38294640181236056175007289 28720980135927042131255467)
    ·
      refine ⟨43081470203890563196883201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28720980135927042131255467 43081470203890563196883201)
      ·
        refine ⟨32311102652917922397662401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43081470203890563196883201 32311102652917922397662401)
        ·
          refine ⟨24233326989688441798246801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32311102652917922397662401 24233326989688441798246801)
          ·
            refine ⟨18174995242266331348685101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24233326989688441798246801 18174995242266331348685101)
            ·
              refine ⟨6815623215849874255756913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18174995242266331348685101 6815623215849874255756913)
              ·
                refine ⟨5111717411887405691817685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6815623215849874255756913 5111717411887405691817685)
                ·
                  refine ⟨119805876841111070901977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5111717411887405691817685 119805876841111070901977)
                  ·
                    rfl

theorem cell22_1049945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 2, 7].length) (baseStart_1049945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1049945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1049945 prefixEnd_1049945 := by exact prefixLift 1049945
  have htrace : WordTrace (prefixWord ++ tailWord_1049945) baseStart_1049945 baseEnd_1049945 := by
    simpa [prefixWord, tailWord_1049945, baseEnd_1049945] using wordTrace_append hprefix tailTrace_1049945
  have hstable : (prefixWord ++ tailWord_1049945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1049945).length < 2 ^ (prefixWord ++ tailWord_1049945).sum := by decide
  have hdescent : baseEnd_1049945 < baseStart_1049945 := by decide
  rcases family_descends (prefixWord ++ tailWord_1049945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050039 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 2, 3]
def baseStart_1050039 : Nat := 118140960795 + 1050039 * 2 ^ 59
def prefixEnd_1050039 : Nat := 4983230072969 + 3 ^ 40 * 1050039 * 2
def baseEnd_1050039 : Nat := 359449808644348300855643

theorem tailTrace_1050039 : CollatzResearch.WordTrace tailWord_1050039 prefixEnd_1050039 359449808644348300855643 := by
  unfold tailWord_1050039
  simp only [CollatzResearch.WordTrace]
  refine ⟨38298068642895510228929171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25532045761930340152619447 38298068642895510228929171)
  ·
    refine ⟨57447102964343265343393757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38298068642895510228929171 57447102964343265343393757)
    ·
      refine ⟨21542663611628724503772659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57447102964343265343393757 21542663611628724503772659)
      ·
        refine ⟨32313995417443086755658989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21542663611628724503772659 32313995417443086755658989)
        ·
          refine ⟨12117748281541157533372121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32313995417443086755658989 12117748281541157533372121)
          ·
            refine ⟨9088311211155868150029091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12117748281541157533372121 9088311211155868150029091)
            ·
              refine ⟨13632466816733802225043637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9088311211155868150029091 13632466816733802225043637)
              ·
                refine ⟨1278043764068793958597841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13632466816733802225043637 1278043764068793958597841)
                ·
                  refine ⟨958532823051595468948381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1278043764068793958597841 958532823051595468948381)
                  ·
                    refine ⟨359449808644348300855643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958532823051595468948381 359449808644348300855643)
                    ·
                      rfl

theorem cell22_1050039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 3].length) (baseStart_1050039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050039 prefixEnd_1050039 := by exact prefixLift 1050039
  have htrace : WordTrace (prefixWord ++ tailWord_1050039) baseStart_1050039 baseEnd_1050039 := by
    simpa [prefixWord, tailWord_1050039, baseEnd_1050039] using wordTrace_append hprefix tailTrace_1050039
  have hstable : (prefixWord ++ tailWord_1050039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050039).length < 2 ^ (prefixWord ++ tailWord_1050039).sum := by decide
  have hdescent : baseEnd_1050039 < baseStart_1050039 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050309 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 3, 5]
def baseStart_1050309 : Nat := 118140960795 + 1050309 * 2 ^ 59
def prefixEnd_1050309 : Nat := 4983230072969 + 3 ^ 40 * 1050309 * 2
def baseEnd_1050309 : Nat := 359542235162157596604815

theorem tailTrace_1050309 : CollatzResearch.WordTrace tailWord_1050309 prefixEnd_1050309 359542235162157596604815 := by
  unfold tailWord_1050309
  simp only [CollatzResearch.WordTrace]
  refine ⟨38307916351917346341257981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25538610901278230894171987 38307916351917346341257981)
  ·
    refine ⟨14365468631969004877971743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38307916351917346341257981 14365468631969004877971743)
    ·
      refine ⟨21548202947953507316957615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14365468631969004877971743 21548202947953507316957615)
      ·
        refine ⟨32322304421930260975436423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21548202947953507316957615 32322304421930260975436423)
        ·
          refine ⟨48483456632895391463154635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32322304421930260975436423 48483456632895391463154635)
          ·
            refine ⟨72725184949343087194731953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48483456632895391463154635 72725184949343087194731953)
            ·
              refine ⟨54543888712007315396048965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72725184949343087194731953 54543888712007315396048965)
              ·
                refine ⟨10226979133501371636759181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54543888712007315396048965 10226979133501371636759181)
                ·
                  refine ⟨3835117175063014363784693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10226979133501371636759181 3835117175063014363784693)
                  ·
                    refine ⟨359542235162157596604815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3835117175063014363784693 359542235162157596604815)
                    ·
                      rfl

theorem cell22_1050309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_1050309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050309 prefixEnd_1050309 := by exact prefixLift 1050309
  have htrace : WordTrace (prefixWord ++ tailWord_1050309) baseStart_1050309 baseEnd_1050309 := by
    simpa [prefixWord, tailWord_1050309, baseEnd_1050309] using wordTrace_append hprefix tailTrace_1050309
  have hstable : (prefixWord ++ tailWord_1050309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050309).length < 2 ^ (prefixWord ++ tailWord_1050309).sum := by decide
  have hdescent : baseEnd_1050309 < baseStart_1050309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050317 : List Nat := [1, 6, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1050317 : Nat := 118140960795 + 1050317 * 2 ^ 59
def prefixEnd_1050317 : Nat := 4983230072969 + 3 ^ 40 * 1050317 * 2
def baseEnd_1050317 : Nat := 119848324575216080801597

theorem tailTrace_1050317 : CollatzResearch.WordTrace tailWord_1050317 prefixEnd_1050317 119848324575216080801597 := by
  unfold tailWord_1050317
  simp only [CollatzResearch.WordTrace]
  refine ⟨38308208135888363707549205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25538805423925575805032803 38308208135888363707549205)
  ·
    refine ⟨1795697256369767048791369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 38308208135888363707549205 1795697256369767048791369)
    ·
      refine ⟨1346772942277325286593527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1795697256369767048791369 1346772942277325286593527)
      ·
        refine ⟨2020159413415987929890291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1346772942277325286593527 2020159413415987929890291)
        ·
          refine ⟨3030239120123981894835437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020159413415987929890291 3030239120123981894835437)
          ·
            refine ⟨1136339670046493210563289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3030239120123981894835437 1136339670046493210563289)
            ·
              refine ⟨852254752534869907922467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1136339670046493210563289 852254752534869907922467)
              ·
                refine ⟨1278382128802304861883701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852254752534869907922467 1278382128802304861883701)
                ·
                  refine ⟨119848324575216080801597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1278382128802304861883701 119848324575216080801597)
                  ·
                    rfl

theorem cell22_1050317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1050317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050317 prefixEnd_1050317 := by exact prefixLift 1050317
  have htrace : WordTrace (prefixWord ++ tailWord_1050317) baseStart_1050317 baseEnd_1050317 := by
    simpa [prefixWord, tailWord_1050317, baseEnd_1050317] using wordTrace_append hprefix tailTrace_1050317
  have hstable : (prefixWord ++ tailWord_1050317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050317).length < 2 ^ (prefixWord ++ tailWord_1050317).sum := by decide
  have hdescent : baseEnd_1050317 < baseStart_1050317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050358 : List Nat := [5, 1, 1, 1, 1, 3, 2, 2, 2, 4]
def baseStart_1050358 : Nat := 118140960795 + 1050358 * 2 ^ 59
def prefixEnd_1050358 : Nat := 4983230072969 + 3 ^ 40 * 1050358 * 2
def baseEnd_1050358 : Nat := 359559008863537802129665

theorem tailTrace_1050358 : CollatzResearch.WordTrace tailWord_1050358 prefixEnd_1050358 359559008863537802129665 := by
  unfold tailWord_1050358
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394356470546239231861983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25539802352493218473194485 2394356470546239231861983)
  ·
    refine ⟨3591534705819358847792975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2394356470546239231861983 3591534705819358847792975)
    ·
      refine ⟨5387302058729038271689463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3591534705819358847792975 5387302058729038271689463)
      ·
        refine ⟨8080953088093557407534195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5387302058729038271689463 8080953088093557407534195)
        ·
          refine ⟨12121429632140336111301293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8080953088093557407534195 12121429632140336111301293)
          ·
            refine ⟨4545536112052626041737985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12121429632140336111301293 4545536112052626041737985)
            ·
              refine ⟨3409152084039469531303489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4545536112052626041737985 3409152084039469531303489)
              ·
                refine ⟨2556864063029602148477617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3409152084039469531303489 2556864063029602148477617)
                ·
                  refine ⟨1917648047272201611358213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2556864063029602148477617 1917648047272201611358213)
                  ·
                    refine ⟨359559008863537802129665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1917648047272201611358213 359559008863537802129665)
                    ·
                      rfl

theorem cell22_1050358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 2, 2, 2, 4].length) (baseStart_1050358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050358 prefixEnd_1050358 := by exact prefixLift 1050358
  have htrace : WordTrace (prefixWord ++ tailWord_1050358) baseStart_1050358 baseEnd_1050358 := by
    simpa [prefixWord, tailWord_1050358, baseEnd_1050358] using wordTrace_append hprefix tailTrace_1050358
  have hstable : (prefixWord ++ tailWord_1050358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050358).length < 2 ^ (prefixWord ++ tailWord_1050358).sum := by decide
  have hdescent : baseEnd_1050358 < baseStart_1050358 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050405 : List Nat := [1, 3, 1, 2, 3, 2, 1, 5, 1, 3]
def baseStart_1050405 : Nat := 118140960795 + 1050405 * 2 ^ 59
def prefixEnd_1050405 : Nat := 4983230072969 + 3 ^ 40 * 1050405 * 2
def baseEnd_1050405 : Nat := 359575097924045346204521

theorem tailTrace_1050405 : CollatzResearch.WordTrace tailWord_1050405 prefixEnd_1050405 359575097924045346204521 := by
  unfold tailWord_1050405
  simp only [CollatzResearch.WordTrace]
  refine ⟨38311417759569554736752669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25540945173046369824501779 38311417759569554736752669)
  ·
    refine ⟨14366781659838583026282251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38311417759569554736752669 14366781659838583026282251)
    ·
      refine ⟨21550172489757874539423377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14366781659838583026282251 21550172489757874539423377)
      ·
        refine ⟨16162629367318405904567533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21550172489757874539423377 16162629367318405904567533)
        ·
          refine ⟨6060986012744402214212825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16162629367318405904567533 6060986012744402214212825)
          ·
            refine ⟨4545739509558301660659619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6060986012744402214212825 4545739509558301660659619)
            ·
              refine ⟨6818609264337452490989429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4545739509558301660659619 6818609264337452490989429)
              ·
                refine ⟨639244618531636171030259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6818609264337452490989429 639244618531636171030259)
                ·
                  refine ⟨958866927797454256545389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639244618531636171030259 958866927797454256545389)
                  ·
                    refine ⟨359575097924045346204521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958866927797454256545389 359575097924045346204521)
                    ·
                      rfl

theorem cell22_1050405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_1050405 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050405 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050405 prefixEnd_1050405 := by exact prefixLift 1050405
  have htrace : WordTrace (prefixWord ++ tailWord_1050405) baseStart_1050405 baseEnd_1050405 := by
    simpa [prefixWord, tailWord_1050405, baseEnd_1050405] using wordTrace_append hprefix tailTrace_1050405
  have hstable : (prefixWord ++ tailWord_1050405).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050405).length < 2 ^ (prefixWord ++ tailWord_1050405).sum := by decide
  have hdescent : baseEnd_1050405 < baseStart_1050405 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050418 : List Nat := [3, 2, 1, 1, 3, 2, 3, 2, 5]
def baseStart_1050418 : Nat := 118140960795 + 1050418 * 2 ^ 59
def prefixEnd_1050418 : Nat := 4983230072969 + 3 ^ 40 * 1050418 * 2
def baseEnd_1050418 : Nat := 119859849363239215209827

theorem tailTrace_1050418 : CollatzResearch.WordTrace tailWord_1050418 prefixEnd_1050418 119859849363239215209827 := by
  unfold tailWord_1050418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9577972977130614489243977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25541261272348305304650605 9577972977130614489243977)
  ·
    refine ⟨7183479732847960866932983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9577972977130614489243977 7183479732847960866932983)
    ·
      refine ⟨10775219599271941300399475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7183479732847960866932983 10775219599271941300399475)
      ·
        refine ⟨16162829398907911950599213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10775219599271941300399475 16162829398907911950599213)
        ·
          refine ⟨6061061024590466981474705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16162829398907911950599213 6061061024590466981474705)
          ·
            refine ⟨4545795768442850236106029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6061061024590466981474705 4545795768442850236106029)
            ·
              refine ⟨1704673413166068838539761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4545795768442850236106029 1704673413166068838539761)
              ·
                refine ⟨1278505059874551628904821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1704673413166068838539761 1278505059874551628904821)
                ·
                  refine ⟨119859849363239215209827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1278505059874551628904821 119859849363239215209827)
                  ·
                    rfl

theorem cell22_1050418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 2, 5].length) (baseStart_1050418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050418 prefixEnd_1050418 := by exact prefixLift 1050418
  have htrace : WordTrace (prefixWord ++ tailWord_1050418) baseStart_1050418 baseEnd_1050418 := by
    simpa [prefixWord, tailWord_1050418, baseEnd_1050418] using wordTrace_append hprefix tailTrace_1050418
  have hstable : (prefixWord ++ tailWord_1050418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050418).length < 2 ^ (prefixWord ++ tailWord_1050418).sum := by decide
  have hdescent : baseEnd_1050418 < baseStart_1050418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050422 : List Nat := [5, 1, 2, 2, 1, 2, 2, 1, 3, 3]
def baseStart_1050422 : Nat := 118140960795 + 1050422 * 2 ^ 59
def prefixEnd_1050422 : Nat := 4983230072969 + 3 ^ 40 * 1050422 * 2
def baseEnd_1050422 : Nat := 359580917371462968529469

theorem tailTrace_1050422 : CollatzResearch.WordTrace tailWord_1050422 prefixEnd_1050422 359580917371462968529469 := by
  unfold tailWord_1050422
  simp only [CollatzResearch.WordTrace]
  refine ⟨2394502362531747915007595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25541358533671977760081013 2394502362531747915007595)
  ·
    refine ⟨3591753543797621872511393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2394502362531747915007595 3591753543797621872511393)
    ·
      refine ⟨2693815157848216404383545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3591753543797621872511393 2693815157848216404383545)
      ·
        refine ⟨2020361368386162303287659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2693815157848216404383545 2020361368386162303287659)
        ·
          refine ⟨3030542052579243454931489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2020361368386162303287659 3030542052579243454931489)
          ·
            refine ⟨2272906539434432591198617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3030542052579243454931489 2272906539434432591198617)
            ·
              refine ⟨1704679904575824443398963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2272906539434432591198617 1704679904575824443398963)
              ·
                refine ⟨2557019856863736665098445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1704679904575824443398963 2557019856863736665098445)
                ·
                  refine ⟨958882446323901249411917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2557019856863736665098445 958882446323901249411917)
                  ·
                    refine ⟨359580917371462968529469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 958882446323901249411917 359580917371462968529469)
                    ·
                      rfl

theorem cell22_1050422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_1050422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050422 prefixEnd_1050422 := by exact prefixLift 1050422
  have htrace : WordTrace (prefixWord ++ tailWord_1050422) baseStart_1050422 baseEnd_1050422 := by
    simpa [prefixWord, tailWord_1050422, baseEnd_1050422] using wordTrace_append hprefix tailTrace_1050422
  have hstable : (prefixWord ++ tailWord_1050422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050422).length < 2 ^ (prefixWord ++ tailWord_1050422).sum := by decide
  have hdescent : baseEnd_1050422 < baseStart_1050422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050553 : List Nat := [1, 2, 1, 4, 2, 1, 1, 5, 5]
def baseStart_1050553 : Nat := 118140960795 + 1050553 * 2 ^ 59
def prefixEnd_1050553 : Nat := 4983230072969 + 3 ^ 40 * 1050553 * 2
def baseEnd_1050553 : Nat := 119875253782874097834689

theorem tailTrace_1050553 : CollatzResearch.WordTrace tailWord_1050553 prefixEnd_1050553 119875253782874097834689 := by
  unfold tailWord_1050553
  simp only [CollatzResearch.WordTrace]
  refine ⟨38316815763033376013140313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25544543842022250675426875 38316815763033376013140313)
  ·
    refine ⟨28737611822275032009855235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38316815763033376013140313 28737611822275032009855235)
    ·
      refine ⟨43106417733412548014782853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28737611822275032009855235 43106417733412548014782853)
      ·
        refine ⟨8082453325014852752771785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43106417733412548014782853 8082453325014852752771785)
        ·
          refine ⟨6061839993761139564578839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8082453325014852752771785 6061839993761139564578839)
          ·
            refine ⟨9092759990641709346868259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6061839993761139564578839 9092759990641709346868259)
            ·
              refine ⟨13639139985962564020302389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9092759990641709346868259 13639139985962564020302389)
              ·
                refine ⟨1278669373683990376903349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13639139985962564020302389 1278669373683990376903349)
                ·
                  refine ⟨119875253782874097834689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1278669373683990376903349 119875253782874097834689)
                  ·
                    rfl

theorem cell22_1050553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 5, 5].length) (baseStart_1050553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050553 prefixEnd_1050553 := by exact prefixLift 1050553
  have htrace : WordTrace (prefixWord ++ tailWord_1050553) baseStart_1050553 baseEnd_1050553 := by
    simpa [prefixWord, tailWord_1050553, baseEnd_1050553] using wordTrace_append hprefix tailTrace_1050553
  have hstable : (prefixWord ++ tailWord_1050553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050553).length < 2 ^ (prefixWord ++ tailWord_1050553).sum := by decide
  have hdescent : baseEnd_1050553 < baseStart_1050553 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050675 : List Nat := [1, 1, 1, 2, 4, 1, 2, 4, 3, 3]
def baseStart_1050675 : Nat := 118140960795 + 1050675 * 2 ^ 59
def prefixEnd_1050675 : Nat := 4983230072969 + 3 ^ 40 * 1050675 * 2
def baseEnd_1050675 : Nat := 359667524441854641953693

theorem tailTrace_1050675 : CollatzResearch.WordTrace tailWord_1050675 prefixEnd_1050675 359667524441854641953693 := by
  unfold tailWord_1050675
  simp only [CollatzResearch.WordTrace]
  refine ⟨38321265468591390849081479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25547510312394260566054319 38321265468591390849081479)
  ·
    refine ⟨57481898202887086273622219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38321265468591390849081479 57481898202887086273622219)
    ·
      refine ⟨86222847304330629410433329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57481898202887086273622219 86222847304330629410433329)
      ·
        refine ⟨64667135478247972057824997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86222847304330629410433329 64667135478247972057824997)
        ·
          refine ⟨12125087902171494760842187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64667135478247972057824997 12125087902171494760842187)
          ·
            refine ⟨18187631853257242141263281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12125087902171494760842187 18187631853257242141263281)
            ·
              refine ⟨13640723889942931605947461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18187631853257242141263281 13640723889942931605947461)
              ·
                refine ⟨2557635729364299676115149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13640723889942931605947461 2557635729364299676115149)
                ·
                  refine ⟨959113398511612378543181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2557635729364299676115149 959113398511612378543181)
                  ·
                    refine ⟨359667524441854641953693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959113398511612378543181 359667524441854641953693)
                    ·
                      rfl

theorem cell22_1050675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 4, 3, 3].length) (baseStart_1050675 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050675 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050675 prefixEnd_1050675 := by exact prefixLift 1050675
  have htrace : WordTrace (prefixWord ++ tailWord_1050675) baseStart_1050675 baseEnd_1050675 := by
    simpa [prefixWord, tailWord_1050675, baseEnd_1050675] using wordTrace_append hprefix tailTrace_1050675
  have hstable : (prefixWord ++ tailWord_1050675).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050675).length < 2 ^ (prefixWord ++ tailWord_1050675).sum := by decide
  have hdescent : baseEnd_1050675 < baseStart_1050675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050703 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 4, 5]
def baseStart_1050703 : Nat := 118140960795 + 1050703 * 2 ^ 59
def prefixEnd_1050703 : Nat := 4983230072969 + 3 ^ 40 * 1050703 * 2
def baseEnd_1050703 : Nat := 359677109414071902253607

theorem tailTrace_1050703 : CollatzResearch.WordTrace tailWord_1050703 prefixEnd_1050703 359677109414071902253607 := by
  unfold tailWord_1050703
  simp only [CollatzResearch.WordTrace]
  refine ⟨38322286712489951631100763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25548191141659967754067175 38322286712489951631100763)
  ·
    refine ⟨57483430068734927446651145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38322286712489951631100763 57483430068734927446651145)
    ·
      refine ⟨43112572551551195584988359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57483430068734927446651145 43112572551551195584988359)
      ·
        refine ⟨64668858827326793377482539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43112572551551195584988359 64668858827326793377482539)
        ·
          refine ⟨97003288240990190066223809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64668858827326793377482539 97003288240990190066223809)
          ·
            refine ⟨72752466180742642549667857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97003288240990190066223809 72752466180742642549667857)
            ·
              refine ⟨54564349635556981912250893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72752466180742642549667857 54564349635556981912250893)
              ·
                refine ⟨20461631113333868217094085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54564349635556981912250893 20461631113333868217094085)
                ·
                  refine ⟨3836555833750100290705141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20461631113333868217094085 3836555833750100290705141)
                  ·
                    refine ⟨359677109414071902253607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3836555833750100290705141 359677109414071902253607)
                    ·
                      rfl

theorem cell22_1050703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 5].length) (baseStart_1050703 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050703 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050703 prefixEnd_1050703 := by exact prefixLift 1050703
  have htrace : WordTrace (prefixWord ++ tailWord_1050703) baseStart_1050703 baseEnd_1050703 := by
    simpa [prefixWord, tailWord_1050703, baseEnd_1050703] using wordTrace_append hprefix tailTrace_1050703
  have hstable : (prefixWord ++ tailWord_1050703).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050703).length < 2 ^ (prefixWord ++ tailWord_1050703).sum := by decide
  have hdescent : baseEnd_1050703 < baseStart_1050703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050709 : List Nat := [1, 3, 2, 2, 1, 4, 1, 4, 1, 3]
def baseStart_1050709 : Nat := 118140960795 + 1050709 * 2 ^ 59
def prefixEnd_1050709 : Nat := 4983230072969 + 3 ^ 40 * 1050709 * 2
def baseEnd_1050709 : Nat := 359679163336689886603589

theorem tailTrace_1050709 : CollatzResearch.WordTrace tailWord_1050709 prefixEnd_1050709 359679163336689886603589 := by
  unfold tailWord_1050709
  simp only [CollatzResearch.WordTrace]
  refine ⟨38322505550468214655819181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25548337033645476437212787 38322505550468214655819181)
  ·
    refine ⟨14370939581425580495932193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38322505550468214655819181 14370939581425580495932193)
    ·
      refine ⟨10778204686069185371949145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14370939581425580495932193 10778204686069185371949145)
      ·
        refine ⟨8083653514551889028961859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10778204686069185371949145 8083653514551889028961859)
        ·
          refine ⟨12125480271827833543442789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8083653514551889028961859 12125480271827833543442789)
          ·
            refine ⟨2273527550967718789395523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12125480271827833543442789 2273527550967718789395523)
            ·
              refine ⟨3410291326451578184093285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273527550967718789395523 3410291326451578184093285)
              ·
                refine ⟨639429623709670909517491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3410291326451578184093285 639429623709670909517491)
                ·
                  refine ⟨959144435564506364276237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639429623709670909517491 959144435564506364276237)
                  ·
                    refine ⟨359679163336689886603589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959144435564506364276237 359679163336689886603589)
                    ·
                      rfl

theorem cell22_1050709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_1050709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050709 prefixEnd_1050709 := by exact prefixLift 1050709
  have htrace : WordTrace (prefixWord ++ tailWord_1050709) baseStart_1050709 baseEnd_1050709 := by
    simpa [prefixWord, tailWord_1050709, baseEnd_1050709] using wordTrace_append hprefix tailTrace_1050709
  have hstable : (prefixWord ++ tailWord_1050709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050709).length < 2 ^ (prefixWord ++ tailWord_1050709).sum := by decide
  have hdescent : baseEnd_1050709 < baseStart_1050709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050720 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 2, 5]
def baseStart_1050720 : Nat := 118140960795 + 1050720 * 2 ^ 59
def prefixEnd_1050720 : Nat := 4983230072969 + 3 ^ 40 * 1050720 * 2
def baseEnd_1050720 : Nat := 359682928861489524578555

theorem tailTrace_1050720 : CollatzResearch.WordTrace tailWord_1050720 prefixEnd_1050720 359682928861489524578555 := by
  unfold tailWord_1050720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19161453376714181767234807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25548604502285575689646409 19161453376714181767234807)
  ·
    refine ⟨28742180065071272650852211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19161453376714181767234807 28742180065071272650852211)
    ·
      refine ⟨43113270097606908976278317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28742180065071272650852211 43113270097606908976278317)
      ·
        refine ⟨16167476286602590866104369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43113270097606908976278317 16167476286602590866104369)
        ·
          refine ⟨12125607214951943149578277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16167476286602590866104369 12125607214951943149578277)
          ·
            refine ⟨2273551352803489340545927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12125607214951943149578277 2273551352803489340545927)
            ·
              refine ⟨3410327029205234010818891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273551352803489340545927 3410327029205234010818891)
              ·
                refine ⟨5115490543807851016228337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410327029205234010818891 5115490543807851016228337)
                ·
                  refine ⟨3836617907855888262171253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5115490543807851016228337 3836617907855888262171253)
                  ·
                    refine ⟨359682928861489524578555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3836617907855888262171253 359682928861489524578555)
                    ·
                      rfl

theorem cell22_1050720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 5].length) (baseStart_1050720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050720 prefixEnd_1050720 := by exact prefixLift 1050720
  have htrace : WordTrace (prefixWord ++ tailWord_1050720) baseStart_1050720 baseEnd_1050720 := by
    simpa [prefixWord, tailWord_1050720, baseEnd_1050720] using wordTrace_append hprefix tailTrace_1050720
  have hstable : (prefixWord ++ tailWord_1050720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050720).length < 2 ^ (prefixWord ++ tailWord_1050720).sum := by decide
  have hdescent : baseEnd_1050720 < baseStart_1050720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050735 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 3, 4]
def baseStart_1050735 : Nat := 118140960795 + 1050735 * 2 ^ 59
def prefixEnd_1050735 : Nat := 4983230072969 + 3 ^ 40 * 1050735 * 2
def baseEnd_1050735 : Nat := 359688063668034485453509

theorem tailTrace_1050735 : CollatzResearch.WordTrace tailWord_1050735 prefixEnd_1050735 359688063668034485453509 := by
  unfold tailWord_1050735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38323453848374021096265659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25548969232249347397510439 38323453848374021096265659)
  ·
    refine ⟨57485180772561031644398489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38323453848374021096265659 57485180772561031644398489)
    ·
      refine ⟨43113885579420773733298867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57485180772561031644398489 43113885579420773733298867)
      ·
        refine ⟨64670828369131160599948301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43113885579420773733298867 64670828369131160599948301)
        ·
          refine ⟨24251560638424185224980613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64670828369131160599948301 24251560638424185224980613)
          ·
            refine ⟨4547167619704534729683865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24251560638424185224980613 4547167619704534729683865)
            ·
              refine ⟨3410375714778401047262899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547167619704534729683865 3410375714778401047262899)
              ·
                refine ⟨5115563572167601570894349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410375714778401047262899 5115563572167601570894349)
                ·
                  refine ⟨1918336339562850589085381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5115563572167601570894349 1918336339562850589085381)
                  ·
                    refine ⟨359688063668034485453509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1918336339562850589085381 359688063668034485453509)
                    ·
                      rfl

theorem cell22_1050735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 3, 4].length) (baseStart_1050735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050735 prefixEnd_1050735 := by exact prefixLift 1050735
  have htrace : WordTrace (prefixWord ++ tailWord_1050735) baseStart_1050735 baseEnd_1050735 := by
    simpa [prefixWord, tailWord_1050735, baseEnd_1050735] using wordTrace_append hprefix tailTrace_1050735
  have hstable : (prefixWord ++ tailWord_1050735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050735).length < 2 ^ (prefixWord ++ tailWord_1050735).sum := by decide
  have hdescent : baseEnd_1050735 < baseStart_1050735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050780 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 6]
def baseStart_1050780 : Nat := 118140960795 + 1050780 * 2 ^ 59
def prefixEnd_1050780 : Nat := 4983230072969 + 3 ^ 40 * 1050780 * 2
def baseEnd_1050780 : Nat := 359703468087669368078371

theorem tailTrace_1050780 : CollatzResearch.WordTrace tailWord_1050780 prefixEnd_1050780 359703468087669368078371 := by
  unfold tailWord_1050780
  simp only [CollatzResearch.WordTrace]
  refine ⟨19162547566605496890826897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25550063422140662521102529 19162547566605496890826897)
  ·
    refine ⟨14371910674954122668120173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19162547566605496890826897 14371910674954122668120173)
    ·
      refine ⟨5389466503107796000545065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14371910674954122668120173 5389466503107796000545065)
      ·
        refine ⟨4042099877330847000408799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5389466503107796000545065 4042099877330847000408799)
        ·
          refine ⟨6063149815996270500613199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4042099877330847000408799 6063149815996270500613199)
          ·
            refine ⟨9094724723994405750919799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6063149815996270500613199 9094724723994405750919799)
            ·
              refine ⟨13642087085991608626379699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9094724723994405750919799 13642087085991608626379699)
              ·
                refine ⟨20463130628987412939569549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13642087085991608626379699 20463130628987412939569549)
                ·
                  refine ⟨7673673985870279852338581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20463130628987412939569549 7673673985870279852338581)
                  ·
                    refine ⟨359703468087669368078371, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7673673985870279852338581 359703468087669368078371)
                    ·
                      rfl

theorem cell22_1050780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_1050780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050780 prefixEnd_1050780 := by exact prefixLift 1050780
  have htrace : WordTrace (prefixWord ++ tailWord_1050780) baseStart_1050780 baseEnd_1050780 := by
    simpa [prefixWord, tailWord_1050780, baseEnd_1050780] using wordTrace_append hprefix tailTrace_1050780
  have hstable : (prefixWord ++ tailWord_1050780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050780).length < 2 ^ (prefixWord ++ tailWord_1050780).sum := by decide
  have hdescent : baseEnd_1050780 < baseStart_1050780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050797 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 6]
def baseStart_1050797 : Nat := 118140960795 + 1050797 * 2 ^ 59
def prefixEnd_1050797 : Nat := 4983230072969 + 3 ^ 40 * 1050797 * 2
def baseEnd_1050797 : Nat := 359709287535086990403319

theorem tailTrace_1050797 : CollatzResearch.WordTrace tailWord_1050797 prefixEnd_1050797 359709287535086990403319 := by
  unfold tailWord_1050797
  simp only [CollatzResearch.WordTrace]
  refine ⟨38325715174149405685022645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25550476782766270456681763 38325715174149405685022645)
  ·
    refine ⟨3593035797576506782970873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38325715174149405685022645 3593035797576506782970873)
    ·
      refine ⟨2694776848182380087228155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3593035797576506782970873 2694776848182380087228155)
      ·
        refine ⟨4042165272273570130842233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2694776848182380087228155 4042165272273570130842233)
        ·
          refine ⟨3031623954205177598131675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4042165272273570130842233 3031623954205177598131675)
          ·
            refine ⟨4547435931307766397197513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3031623954205177598131675 4547435931307766397197513)
            ·
              refine ⟨3410576948480824797898135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4547435931307766397197513 3410576948480824797898135)
              ·
                refine ⟨5115865422721237196847203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3410576948480824797898135 5115865422721237196847203)
                ·
                  refine ⟨7673798134081855795270805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5115865422721237196847203 7673798134081855795270805)
                  ·
                    refine ⟨359709287535086990403319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7673798134081855795270805 359709287535086990403319)
                    ·
                      rfl

theorem cell22_1050797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 6].length) (baseStart_1050797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050797 prefixEnd_1050797 := by exact prefixLift 1050797
  have htrace : WordTrace (prefixWord ++ tailWord_1050797) baseStart_1050797 baseEnd_1050797 := by
    simpa [prefixWord, tailWord_1050797, baseEnd_1050797] using wordTrace_append hprefix tailTrace_1050797
  have hstable : (prefixWord ++ tailWord_1050797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050797).length < 2 ^ (prefixWord ++ tailWord_1050797).sum := by decide
  have hdescent : baseEnd_1050797 < baseStart_1050797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050801 : List Nat := [1, 2, 2, 5, 2, 2, 1, 3, 4]
def baseStart_1050801 : Nat := 118140960795 + 1050801 * 2 ^ 59
def prefixEnd_1050801 : Nat := 4983230072969 + 3 ^ 40 * 1050801 * 2
def baseEnd_1050801 : Nat := 119903552272277437767769

theorem tailTrace_1050801 : CollatzResearch.WordTrace tailWord_1050801 prefixEnd_1050801 119903552272277437767769 := by
  unfold tailWord_1050801
  simp only [CollatzResearch.WordTrace]
  refine ⟨38325861066134914368168257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25550574044089942912112171 38325861066134914368168257)
  ·
    refine ⟨28744395799601185776126193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38325861066134914368168257 28744395799601185776126193)
    ·
      refine ⟨21558296849700889332094645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28744395799601185776126193 21558296849700889332094645)
      ·
        refine ⟨2021090329659458374883873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21558296849700889332094645 2021090329659458374883873)
        ·
          refine ⟨1515817747244593781162905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021090329659458374883873 1515817747244593781162905)
          ·
            refine ⟨1136863310433445335872179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515817747244593781162905 1136863310433445335872179)
            ·
              refine ⟨1705294965650168003808269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1136863310433445335872179 1705294965650168003808269)
              ·
                refine ⟨639485612118813001428101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1705294965650168003808269 639485612118813001428101)
                ·
                  refine ⟨119903552272277437767769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 639485612118813001428101 119903552272277437767769)
                  ·
                    rfl

theorem cell22_1050801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 2, 1, 3, 4].length) (baseStart_1050801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050801 prefixEnd_1050801 := by exact prefixLift 1050801
  have htrace : WordTrace (prefixWord ++ tailWord_1050801) baseStart_1050801 baseEnd_1050801 := by
    simpa [prefixWord, tailWord_1050801, baseEnd_1050801] using wordTrace_append hprefix tailTrace_1050801
  have hstable : (prefixWord ++ tailWord_1050801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050801).length < 2 ^ (prefixWord ++ tailWord_1050801).sum := by decide
  have hdescent : baseEnd_1050801 < baseStart_1050801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050812 : List Nat := [2, 2, 2, 3, 3, 2, 8]
def baseStart_1050812 : Nat := 118140960795 + 1050812 * 2 ^ 59
def prefixEnd_1050812 : Nat := 4983230072969 + 3 ^ 40 * 1050812 * 2
def baseEnd_1050812 : Nat := 13322756383023405602899

theorem tailTrace_1050812 : CollatzResearch.WordTrace tailWord_1050812 prefixEnd_1050812 13322756383023405602899 := by
  unfold tailWord_1050812
  simp only [CollatzResearch.WordTrace]
  refine ⟨19163131134547531623409345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25550841512730042164545793 19163131134547531623409345)
  ·
    refine ⟨14372348350910648717557009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19163131134547531623409345 14372348350910648717557009)
    ·
      refine ⟨10779261263182986538167757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14372348350910648717557009 10779261263182986538167757)
      ·
        refine ⟨4042222973693619951812909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10779261263182986538167757 4042222973693619951812909)
        ·
          refine ⟨1515833615135107481929841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4042222973693619951812909 1515833615135107481929841)
          ·
            refine ⟨1136875211351330611447381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1515833615135107481929841 1136875211351330611447381)
            ·
              refine ⟨13322756383023405602899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1136875211351330611447381 13322756383023405602899)
              ·
                rfl

theorem cell22_1050812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 2, 8].length) (baseStart_1050812 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050812 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050812 prefixEnd_1050812 := by exact prefixLift 1050812
  have htrace : WordTrace (prefixWord ++ tailWord_1050812) baseStart_1050812 baseEnd_1050812 := by
    simpa [prefixWord, tailWord_1050812, baseEnd_1050812] using wordTrace_append hprefix tailTrace_1050812
  have hstable : (prefixWord ++ tailWord_1050812).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050812).length < 2 ^ (prefixWord ++ tailWord_1050812).sum := by decide
  have hdescent : baseEnd_1050812 < baseStart_1050812 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050814 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 2, 4]
def baseStart_1050814 : Nat := 118140960795 + 1050814 * 2 ^ 59
def prefixEnd_1050814 : Nat := 4983230072969 + 3 ^ 40 * 1050814 * 2
def baseEnd_1050814 : Nat := 359715106982504612728267

theorem tailTrace_1050814 : CollatzResearch.WordTrace tailWord_1050814 prefixEnd_1050814 359715106982504612728267 := by
  unfold tailWord_1050814
  simp only [CollatzResearch.WordTrace]
  refine ⟨4790791901885977198548937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25550890143391878392260997 4790791901885977198548937)
  ·
    refine ⟨3593093926414482898911703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4790791901885977198548937 3593093926414482898911703)
    ·
      refine ⟨5389640889621724348367555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593093926414482898911703 5389640889621724348367555)
      ·
        refine ⟨8084461334432586522551333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5389640889621724348367555 8084461334432586522551333)
        ·
          refine ⟨1515836500206109972978375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8084461334432586522551333 1515836500206109972978375)
          ·
            refine ⟨2273754750309164959467563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1515836500206109972978375 2273754750309164959467563)
            ·
              refine ⟨3410632125463747439201345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2273754750309164959467563 3410632125463747439201345)
              ·
                refine ⟨2557974094097810579401009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3410632125463747439201345 2557974094097810579401009)
                ·
                  refine ⟨1918480570573357934550757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2557974094097810579401009 1918480570573357934550757)
                  ·
                    refine ⟨359715106982504612728267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1918480570573357934550757 359715106982504612728267)
                    ·
                      rfl

theorem cell22_1050814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 4].length) (baseStart_1050814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050814 prefixEnd_1050814 := by exact prefixLift 1050814
  have htrace : WordTrace (prefixWord ++ tailWord_1050814) baseStart_1050814 baseEnd_1050814 := by
    simpa [prefixWord, tailWord_1050814, baseEnd_1050814] using wordTrace_append hprefix tailTrace_1050814
  have hstable : (prefixWord ++ tailWord_1050814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050814).length < 2 ^ (prefixWord ++ tailWord_1050814).sum := by decide
  have hdescent : baseEnd_1050814 < baseStart_1050814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050951 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 2, 3]
def baseStart_1050951 : Nat := 118140960795 + 1050951 * 2 ^ 59
def prefixEnd_1050951 : Nat := 4983230072969 + 3 ^ 40 * 1050951 * 2
def baseEnd_1050951 : Nat := 359762004882281922052847

theorem tailTrace_1050951 : CollatzResearch.WordTrace tailWord_1050951 prefixEnd_1050951 359762004882281922052847 := by
  unfold tailWord_1050951
  simp only [CollatzResearch.WordTrace]
  refine ⟨38331332015591489986128707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25554221343727659990752471 38331332015591489986128707)
  ·
    refine ⟨57496998023387234979193061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38331332015591489986128707 57496998023387234979193061)
    ·
      refine ⟨10780687129385106558598699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57496998023387234979193061 10780687129385106558598699)
      ·
        refine ⟨16171030694077659837898049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10780687129385106558598699 16171030694077659837898049)
        ·
          refine ⟨12128273020558244878423537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16171030694077659837898049 12128273020558244878423537)
          ·
            refine ⟨9096204765418683658817653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12128273020558244878423537 9096204765418683658817653)
            ·
              refine ⟨852769196758001593014155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9096204765418683658817653 852769196758001593014155)
              ·
                refine ⟨1279153795137002389521233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852769196758001593014155 1279153795137002389521233)
                ·
                  refine ⟨959365346352751792140925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279153795137002389521233 959365346352751792140925)
                  ·
                    refine ⟨359762004882281922052847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959365346352751792140925 359762004882281922052847)
                    ·
                      rfl

theorem cell22_1050951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 3].length) (baseStart_1050951 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050951 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050951 prefixEnd_1050951 := by exact prefixLift 1050951
  have htrace : WordTrace (prefixWord ++ tailWord_1050951) baseStart_1050951 baseEnd_1050951 := by
    simpa [prefixWord, tailWord_1050951, baseEnd_1050951] using wordTrace_append hprefix tailTrace_1050951
  have hstable : (prefixWord ++ tailWord_1050951).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050951).length < 2 ^ (prefixWord ++ tailWord_1050951).sum := by decide
  have hdescent : baseEnd_1050951 < baseStart_1050951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050964 : List Nat := [2, 4, 1, 1, 2, 2, 4, 6]
def baseStart_1050964 : Nat := 118140960795 + 1050964 * 2 ^ 59
def prefixEnd_1050964 : Nat := 4983230072969 + 3 ^ 40 * 1050964 * 2
def baseEnd_1050964 : Nat := 39974050560883802386423

theorem tailTrace_1050964 : CollatzResearch.WordTrace tailWord_1050964 prefixEnd_1050964 39974050560883802386423 := by
  unfold tailWord_1050964
  simp only [CollatzResearch.WordTrace]
  refine ⟨19165903082272196603175973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25554537443029595470901297 19165903082272196603175973)
  ·
    refine ⟨3593606827926036863095495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19165903082272196603175973 3593606827926036863095495)
    ·
      refine ⟨5390410241889055294643243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3593606827926036863095495 5390410241889055294643243)
      ·
        refine ⟨8085615362833582941964865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5390410241889055294643243 8085615362833582941964865)
        ·
          refine ⟨6064211522125187206473649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8085615362833582941964865 6064211522125187206473649)
          ·
            refine ⟨4548158641593890404855237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6064211522125187206473649 4548158641593890404855237)
            ·
              refine ⟨852779745298854450910357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4548158641593890404855237 852779745298854450910357)
              ·
                refine ⟨39974050560883802386423, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 852779745298854450910357 39974050560883802386423)
                ·
                  rfl

theorem cell22_1050964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 4, 6].length) (baseStart_1050964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050964 prefixEnd_1050964 := by exact prefixLift 1050964
  have htrace : WordTrace (prefixWord ++ tailWord_1050964) baseStart_1050964 baseEnd_1050964 := by
    simpa [prefixWord, tailWord_1050964, baseEnd_1050964] using wordTrace_append hprefix tailTrace_1050964
  have hstable : (prefixWord ++ tailWord_1050964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050964).length < 2 ^ (prefixWord ++ tailWord_1050964).sum := by decide
  have hdescent : baseEnd_1050964 < baseStart_1050964 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1050992 : List Nat := [2, 1, 1, 1, 4, 3, 2, 1, 7]
def baseStart_1050992 : Nat := 118140960795 + 1050992 * 2 ^ 59
def prefixEnd_1050992 : Nat := 4983230072969 + 3 ^ 40 * 1050992 * 2
def baseEnd_1050992 : Nat := 119925346673390493925907

theorem tailTrace_1050992 : CollatzResearch.WordTrace tailWord_1050992 prefixEnd_1050992 119925346673390493925907 := by
  unfold tailWord_1050992
  simp only [CollatzResearch.WordTrace]
  refine ⟨19166413704221476994185615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25555218272295302658914153 19166413704221476994185615)
  ·
    refine ⟨28749620556332215491278423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19166413704221476994185615 28749620556332215491278423)
    ·
      refine ⟨43124430834498323236917635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28749620556332215491278423 43124430834498323236917635)
      ·
        refine ⟨64686646251747484855376453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43124430834498323236917635 64686646251747484855376453)
        ·
          refine ⟨12128746172202653410383085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64686646251747484855376453 12128746172202653410383085)
          ·
            refine ⟨4548279814575995028893657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12128746172202653410383085 4548279814575995028893657)
            ·
              refine ⟨3411209860931996271670243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4548279814575995028893657 3411209860931996271670243)
              ·
                refine ⟨5116814791397994407505365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3411209860931996271670243 5116814791397994407505365)
                ·
                  refine ⟨119925346673390493925907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5116814791397994407505365 119925346673390493925907)
                  ·
                    rfl

theorem cell22_1050992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 1, 7].length) (baseStart_1050992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1050992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1050992 prefixEnd_1050992 := by exact prefixLift 1050992
  have htrace : WordTrace (prefixWord ++ tailWord_1050992) baseStart_1050992 baseEnd_1050992 := by
    simpa [prefixWord, tailWord_1050992, baseEnd_1050992] using wordTrace_append hprefix tailTrace_1050992
  have hstable : (prefixWord ++ tailWord_1050992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1050992).length < 2 ^ (prefixWord ++ tailWord_1050992).sum := by decide
  have hdescent : baseEnd_1050992 < baseStart_1050992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1050992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051052 : List Nat := [2, 2, 1, 1, 1, 1, 3, 1, 5, 5]
def baseStart_1051052 : Nat := 118140960795 + 1051052 * 2 ^ 59
def prefixEnd_1051052 : Nat := 4983230072969 + 3 ^ 40 * 1051052 * 2
def baseEnd_1051052 : Nat := 359796579246351325277537

theorem tailTrace_1051052 : CollatzResearch.WordTrace tailWord_1051052 prefixEnd_1051052 359796579246351325277537 := by
  unfold tailWord_1051052
  simp only [CollatzResearch.WordTrace]
  refine ⟨19167507894112792117777705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25556677192150389490370273 19167507894112792117777705)
  ·
    refine ⟨14375630920584594088333279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19167507894112792117777705 14375630920584594088333279)
    ·
      refine ⟨21563446380876891132499919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14375630920584594088333279 21563446380876891132499919)
      ·
        refine ⟨32345169571315336698749879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21563446380876891132499919 32345169571315336698749879)
        ·
          refine ⟨48517754356973005048124819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32345169571315336698749879 48517754356973005048124819)
          ·
            refine ⟨72776631535459507572187229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48517754356973005048124819 72776631535459507572187229)
            ·
              refine ⟨27291236825797315339570211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72776631535459507572187229 27291236825797315339570211)
              ·
                refine ⟨40936855238695973009355317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27291236825797315339570211 40936855238695973009355317)
                ·
                  refine ⟨3837830178627747469627061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40936855238695973009355317 3837830178627747469627061)
                  ·
                    refine ⟨359796579246351325277537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3837830178627747469627061 359796579246351325277537)
                    ·
                      rfl

theorem cell22_1051052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_1051052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051052 prefixEnd_1051052 := by exact prefixLift 1051052
  have htrace : WordTrace (prefixWord ++ tailWord_1051052) baseStart_1051052 baseEnd_1051052 := by
    simpa [prefixWord, tailWord_1051052, baseEnd_1051052] using wordTrace_append hprefix tailTrace_1051052
  have hstable : (prefixWord ++ tailWord_1051052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051052).length < 2 ^ (prefixWord ++ tailWord_1051052).sum := by decide
  have hdescent : baseEnd_1051052 < baseStart_1051052 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051069 : List Nat := [1, 4, 1, 2, 2, 2, 1, 3, 1, 5]
def baseStart_1051069 : Nat := 118140960795 + 1051069 * 2 ^ 59
def prefixEnd_1051069 : Nat := 4983230072969 + 3 ^ 40 * 1051069 * 2
def baseEnd_1051069 : Nat := 359802398693768947602485

theorem tailTrace_1051069 : CollatzResearch.WordTrace tailWord_1051069 prefixEnd_1051069 359802398693768947602485 := by
  unfold tailWord_1051069
  simp only [CollatzResearch.WordTrace]
  refine ⟨38335635829163996138924261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25557090552775997425949507 38335635829163996138924261)
  ·
    refine ⟨7187931717968249276048299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38335635829163996138924261 7187931717968249276048299)
    ·
      refine ⟨10781897576952373914072449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7187931717968249276048299 10781897576952373914072449)
      ·
        refine ⟨8086423182714280435554337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10781897576952373914072449 8086423182714280435554337)
        ·
          refine ⟨6064817387035710326665753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8086423182714280435554337 6064817387035710326665753)
          ·
            refine ⟨4548613040276782744999315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6064817387035710326665753 4548613040276782744999315)
            ·
              refine ⟨6822919560415174117498973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4548613040276782744999315 6822919560415174117498973)
              ·
                refine ⟨2558594835155690294062115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6822919560415174117498973 2558594835155690294062115)
                ·
                  refine ⟨3837892252733535441093173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2558594835155690294062115 3837892252733535441093173)
                  ·
                    refine ⟨359802398693768947602485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3837892252733535441093173 359802398693768947602485)
                    ·
                      rfl

theorem cell22_1051069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 1, 3, 1, 5].length) (baseStart_1051069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051069 prefixEnd_1051069 := by exact prefixLift 1051069
  have htrace : WordTrace (prefixWord ++ tailWord_1051069) baseStart_1051069 baseEnd_1051069 := by
    simpa [prefixWord, tailWord_1051069, baseEnd_1051069] using wordTrace_append hprefix tailTrace_1051069
  have hstable : (prefixWord ++ tailWord_1051069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051069).length < 2 ^ (prefixWord ++ tailWord_1051069).sum := by decide
  have hdescent : baseEnd_1051069 < baseStart_1051069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051103 : List Nat := [1, 1, 2, 3, 3, 4, 1, 2, 2, 3]
def baseStart_1051103 : Nat := 118140960795 + 1051103 * 2 ^ 59
def prefixEnd_1051103 : Nat := 4983230072969 + 3 ^ 40 * 1051103 * 2
def baseEnd_1051103 : Nat := 359814037588604192252381

theorem tailTrace_1051103 : CollatzResearch.WordTrace tailWord_1051103 prefixEnd_1051103 359814037588604192252381 := by
  unfold tailWord_1051103
  simp only [CollatzResearch.WordTrace]
  refine ⟨38336875911040819945661963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25557917274027213297107975 38336875911040819945661963)
  ·
    refine ⟨57505313866561229918492945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38336875911040819945661963 57505313866561229918492945)
    ·
      refine ⟨43128985399920922438869709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57505313866561229918492945 43128985399920922438869709)
      ·
        refine ⟨16173369524970345914576141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43128985399920922438869709 16173369524970345914576141)
        ·
          refine ⟨6065013571863879717966053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16173369524970345914576141 6065013571863879717966053)
          ·
            refine ⟨1137190044724477447118635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6065013571863879717966053 1137190044724477447118635)
            ·
              refine ⟨1705785067086716170677953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137190044724477447118635 1705785067086716170677953)
              ·
                refine ⟨1279338800315037128008465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1705785067086716170677953 1279338800315037128008465)
                ·
                  refine ⟨959504100236277846006349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279338800315037128008465 959504100236277846006349)
                  ·
                    refine ⟨359814037588604192252381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959504100236277846006349 359814037588604192252381)
                    ·
                      rfl

theorem cell22_1051103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 2, 2, 3].length) (baseStart_1051103 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051103 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051103 prefixEnd_1051103 := by exact prefixLift 1051103
  have htrace : WordTrace (prefixWord ++ tailWord_1051103) baseStart_1051103 baseEnd_1051103 := by
    simpa [prefixWord, tailWord_1051103, baseEnd_1051103] using wordTrace_append hprefix tailTrace_1051103
  have hstable : (prefixWord ++ tailWord_1051103).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051103).length < 2 ^ (prefixWord ++ tailWord_1051103).sum := by decide
  have hdescent : baseEnd_1051103 < baseStart_1051103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051178 : List Nat := [3, 1, 4, 1, 1, 2, 4, 1, 5]
def baseStart_1051178 : Nat := 118140960795 + 1051178 * 2 ^ 59
def prefixEnd_1051178 : Nat := 4983230072969 + 3 ^ 40 * 1051178 * 2
def baseEnd_1051178 : Nat := 119946570540442998875717

theorem tailTrace_1051178 : CollatzResearch.WordTrace tailWord_1051178 prefixEnd_1051178 119946570540442998875717 := by
  unfold tailWord_1051178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9584902846442276938660547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25559740923846071836428125 9584902846442276938660547)
  ·
    refine ⟨14377354269663415407990821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9584902846442276938660547 14377354269663415407990821)
    ·
      refine ⟨2695753925561890388998279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14377354269663415407990821 2695753925561890388998279)
      ·
        refine ⟨4043630888342835583497419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2695753925561890388998279 4043630888342835583497419)
        ·
          refine ⟨6065446332514253375246129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4043630888342835583497419 6065446332514253375246129)
          ·
            refine ⟨4549084749385690031434597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6065446332514253375246129 4549084749385690031434597)
            ·
              refine ⟨852953390509816880893987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4549084749385690031434597 852953390509816880893987)
              ·
                refine ⟨1279430085764725321340981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 852953390509816880893987 1279430085764725321340981)
                ·
                  refine ⟨119946570540442998875717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1279430085764725321340981 119946570540442998875717)
                  ·
                    rfl

theorem cell22_1051178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 4, 1, 5].length) (baseStart_1051178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051178 prefixEnd_1051178 := by exact prefixLift 1051178
  have htrace : WordTrace (prefixWord ++ tailWord_1051178) baseStart_1051178 baseEnd_1051178 := by
    simpa [prefixWord, tailWord_1051178, baseEnd_1051178] using wordTrace_append hprefix tailTrace_1051178
  have hstable : (prefixWord ++ tailWord_1051178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051178).length < 2 ^ (prefixWord ++ tailWord_1051178).sum := by decide
  have hdescent : baseEnd_1051178 < baseStart_1051178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051189 : List Nat := [1, 3, 3, 1, 1, 2, 2, 1, 8]
def baseStart_1051189 : Nat := 118140960795 + 1051189 * 2 ^ 59
def prefixEnd_1051189 : Nat := 4983230072969 + 3 ^ 40 * 1051189 * 2
def baseEnd_1051189 : Nat := 119947825715376211534039

theorem tailTrace_1051189 : CollatzResearch.WordTrace tailWord_1051189 prefixEnd_1051189 119947825715376211534039 := by
  unfold tailWord_1051189
  simp only [CollatzResearch.WordTrace]
  refine ⟨38340012588729256633292621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25560008392486171088861747 38340012588729256633292621)
  ·
    refine ⟨14377504720773471237484733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38340012588729256633292621 14377504720773471237484733)
    ·
      refine ⟨5391564270290051714056775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14377504720773471237484733 5391564270290051714056775)
      ·
        refine ⟨8087346405435077571085163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5391564270290051714056775 8087346405435077571085163)
        ·
          refine ⟨12131019608152616356627745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087346405435077571085163 12131019608152616356627745)
          ·
            refine ⟨9098264706114462267470809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12131019608152616356627745 9098264706114462267470809)
            ·
              refine ⟨6823698529585846700603107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9098264706114462267470809 6823698529585846700603107)
              ·
                refine ⟨10235547794378770050904661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6823698529585846700603107 10235547794378770050904661)
                ·
                  refine ⟨119947825715376211534039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10235547794378770050904661 119947825715376211534039)
                  ·
                    rfl

theorem cell22_1051189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 2, 1, 8].length) (baseStart_1051189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051189 prefixEnd_1051189 := by exact prefixLift 1051189
  have htrace : WordTrace (prefixWord ++ tailWord_1051189) baseStart_1051189 baseEnd_1051189 := by
    simpa [prefixWord, tailWord_1051189, baseEnd_1051189] using wordTrace_append hprefix tailTrace_1051189
  have hstable : (prefixWord ++ tailWord_1051189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051189).length < 2 ^ (prefixWord ++ tailWord_1051189).sum := by decide
  have hdescent : baseEnd_1051189 < baseStart_1051189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051221 : List Nat := [1, 3, 2, 2, 1, 1, 2, 3, 4, 3]
def baseStart_1051221 : Nat := 118140960795 + 1051221 * 2 ^ 59
def prefixEnd_1051221 : Nat := 4983230072969 + 3 ^ 40 * 1051221 * 2
def baseEnd_1051221 : Nat := 359854431400091217802019

theorem tailTrace_1051221 : CollatzResearch.WordTrace tailWord_1051221 prefixEnd_1051221 359854431400091217802019 := by
  unfold tailWord_1051221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38341179724613326098457517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25560786483075550732305011 38341179724613326098457517)
  ·
    refine ⟨14377942396729997286921569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38341179724613326098457517 14377942396729997286921569)
    ·
      refine ⟨10783456797547497965191177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14377942396729997286921569 10783456797547497965191177)
      ·
        refine ⟨8087592598160623473893383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10783456797547497965191177 8087592598160623473893383)
        ·
          refine ⟨12131388897240935210840075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8087592598160623473893383 12131388897240935210840075)
          ·
            refine ⟨18197083345861402816260113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12131388897240935210840075 18197083345861402816260113)
            ·
              refine ⟨13647812509396052112195085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18197083345861402816260113 13647812509396052112195085)
              ·
                refine ⟨5117929691023519542073157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13647812509396052112195085 5117929691023519542073157)
                ·
                  refine ⟨959611817066909914138717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5117929691023519542073157 959611817066909914138717)
                  ·
                    refine ⟨359854431400091217802019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959611817066909914138717 359854431400091217802019)
                    ·
                      rfl

theorem cell22_1051221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_1051221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051221 prefixEnd_1051221 := by exact prefixLift 1051221
  have htrace : WordTrace (prefixWord ++ tailWord_1051221) baseStart_1051221 baseEnd_1051221 := by
    simpa [prefixWord, tailWord_1051221, baseEnd_1051221] using wordTrace_append hprefix tailTrace_1051221
  have hstable : (prefixWord ++ tailWord_1051221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051221).length < 2 ^ (prefixWord ++ tailWord_1051221).sum := by decide
  have hdescent : baseEnd_1051221 < baseStart_1051221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051253 : List Nat := [1, 3, 4, 2, 2, 1, 1, 1, 1, 6]
def baseStart_1051253 : Nat := 118140960795 + 1051253 * 2 ^ 59
def prefixEnd_1051253 : Nat := 4983230072969 + 3 ^ 40 * 1051253 * 2
def baseEnd_1051253 : Nat := 359865385654053801001921

theorem tailTrace_1051253 : CollatzResearch.WordTrace tailWord_1051253 prefixEnd_1051253 359865385654053801001921 := by
  unfold tailWord_1051253
  simp only [CollatzResearch.WordTrace]
  refine ⟨38342346860497395563622413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25561564573664930375748275 38342346860497395563622413)
  ·
    refine ⟨14378380072686523336358405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38342346860497395563622413 14378380072686523336358405)
    ·
      refine ⟨2695946263628723125567201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14378380072686523336358405 2695946263628723125567201)
      ·
        refine ⟨2021959697721542344175401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2695946263628723125567201 2021959697721542344175401)
        ·
          refine ⟨1516469773291156758131551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2021959697721542344175401 1516469773291156758131551)
          ·
            refine ⟨2274704659936735137197327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516469773291156758131551 2274704659936735137197327)
            ·
              refine ⟨3412056989905102705795991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2274704659936735137197327 3412056989905102705795991)
              ·
                refine ⟨5118085484857654058693987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3412056989905102705795991 5118085484857654058693987)
                ·
                  refine ⟨7677128227286481088040981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5118085484857654058693987 7677128227286481088040981)
                  ·
                    refine ⟨359865385654053801001921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7677128227286481088040981 359865385654053801001921)
                    ·
                      rfl

theorem cell22_1051253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_1051253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051253 prefixEnd_1051253 := by exact prefixLift 1051253
  have htrace : WordTrace (prefixWord ++ tailWord_1051253) baseStart_1051253 baseEnd_1051253 := by
    simpa [prefixWord, tailWord_1051253, baseEnd_1051253] using wordTrace_append hprefix tailTrace_1051253
  have hstable : (prefixWord ++ tailWord_1051253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051253).length < 2 ^ (prefixWord ++ tailWord_1051253).sum := by decide
  have hdescent : baseEnd_1051253 < baseStart_1051253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051279 : List Nat := [1, 1, 2, 1, 1, 1, 1, 7, 7]
def baseStart_1051279 : Nat := 118140960795 + 1051279 * 2 ^ 59
def prefixEnd_1051279 : Nat := 4983230072969 + 3 ^ 40 * 1051279 * 2
def baseEnd_1051279 : Nat := 119958095328466133283947

theorem tailTrace_1051279 : CollatzResearch.WordTrace tailWord_1051279 prefixEnd_1051279 119958095328466133283947 := by
  unfold tailWord_1051279
  simp only [CollatzResearch.WordTrace]
  refine ⟨38343295158403202004068891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25562196772268801336045927 38343295158403202004068891)
  ·
    refine ⟨57514942737604803006103337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38343295158403202004068891 57514942737604803006103337)
    ·
      refine ⟨43136207053203602254577503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57514942737604803006103337 43136207053203602254577503)
      ·
        refine ⟨64704310579805403381866255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43136207053203602254577503 64704310579805403381866255)
        ·
          refine ⟨97056465869708105072799383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64704310579805403381866255 97056465869708105072799383)
          ·
            refine ⟨145584698804562157609199075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97056465869708105072799383 145584698804562157609199075)
            ·
              refine ⟨218377048206843236413798613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145584698804562157609199075 218377048206843236413798613)
              ·
                refine ⟨5118212067347888353448405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 218377048206843236413798613 5118212067347888353448405)
                ·
                  refine ⟨119958095328466133283947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5118212067347888353448405 119958095328466133283947)
                  ·
                    rfl

theorem cell22_1051279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 7, 7].length) (baseStart_1051279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051279 prefixEnd_1051279 := by exact prefixLift 1051279
  have htrace : WordTrace (prefixWord ++ tailWord_1051279) baseStart_1051279 baseEnd_1051279 := by
    simpa [prefixWord, tailWord_1051279, baseEnd_1051279] using wordTrace_append hprefix tailTrace_1051279
  have hstable : (prefixWord ++ tailWord_1051279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051279).length < 2 ^ (prefixWord ++ tailWord_1051279).sum := by decide
  have hdescent : baseEnd_1051279 < baseStart_1051279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051317 : List Nat := [1, 3, 3, 3, 1, 1, 3, 3, 1, 3]
def baseStart_1051317 : Nat := 118140960795 + 1051317 * 2 ^ 59
def prefixEnd_1051317 : Nat := 4983230072969 + 3 ^ 40 * 1051317 * 2
def baseEnd_1051317 : Nat := 359887294161978967401725

theorem tailTrace_1051317 : CollatzResearch.WordTrace tailWord_1051317 prefixEnd_1051317 359887294161978967401725 := by
  unfold tailWord_1051317
  simp only [CollatzResearch.WordTrace]
  refine ⟨38344681132265534493952205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25563120754843689662634803 38344681132265534493952205)
  ·
    refine ⟨14379255424599575435232077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38344681132265534493952205 14379255424599575435232077)
    ·
      refine ⟨5392220784224840788212029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14379255424599575435232077 5392220784224840788212029)
      ·
        refine ⟨2022082794084315295579511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5392220784224840788212029 2022082794084315295579511)
        ·
          refine ⟨3033124191126472943369267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022082794084315295579511 3033124191126472943369267)
          ·
            refine ⟨4549686286689709415053901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033124191126472943369267 4549686286689709415053901)
            ·
              refine ⟨1706132357508641030645213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4549686286689709415053901 1706132357508641030645213)
              ·
                refine ⟨639799634065740386491955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1706132357508641030645213 639799634065740386491955)
                ·
                  refine ⟨959699451098610579737933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639799634065740386491955 959699451098610579737933)
                  ·
                    refine ⟨359887294161978967401725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959699451098610579737933 359887294161978967401725)
                    ·
                      rfl

theorem cell22_1051317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_1051317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051317 prefixEnd_1051317 := by exact prefixLift 1051317
  have htrace : WordTrace (prefixWord ++ tailWord_1051317) baseStart_1051317 baseEnd_1051317 := by
    simpa [prefixWord, tailWord_1051317, baseEnd_1051317] using wordTrace_append hprefix tailTrace_1051317
  have hstable : (prefixWord ++ tailWord_1051317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051317).length < 2 ^ (prefixWord ++ tailWord_1051317).sum := by decide
  have hdescent : baseEnd_1051317 < baseStart_1051317 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051373 : List Nat := [1, 5, 1, 2, 1, 1, 3, 2, 1, 5]
def baseStart_1051373 : Nat := 118140960795 + 1051373 * 2 ^ 59
def prefixEnd_1051373 : Nat := 4983230072969 + 3 ^ 40 * 1051373 * 2
def baseEnd_1051373 : Nat := 359906464106413488001553

theorem tailTrace_1051373 : CollatzResearch.WordTrace tailWord_1051373 prefixEnd_1051373 359906464106413488001553 := by
  unfold tailWord_1051373
  simp only [CollatzResearch.WordTrace]
  refine ⟨38346723620062656057990773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25564482413375104038660515 38346723620062656057990773)
  ·
    refine ⟨3595005339380874005436635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38346723620062656057990773 3595005339380874005436635)
    ·
      refine ⟨5392508009071311008154953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595005339380874005436635 5392508009071311008154953)
      ·
        refine ⟨4044381006803483256116215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5392508009071311008154953 4044381006803483256116215)
        ·
          refine ⟨6066571510205224884174323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4044381006803483256116215 6066571510205224884174323)
          ·
            refine ⟨9099857265307837326261485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6066571510205224884174323 9099857265307837326261485)
            ·
              refine ⟨3412446474490438997348057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9099857265307837326261485 3412446474490438997348057)
              ·
                refine ⟨2559334855867829248011043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412446474490438997348057 2559334855867829248011043)
                ·
                  refine ⟨3839002283801743872016565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2559334855867829248011043 3839002283801743872016565)
                  ·
                    refine ⟨359906464106413488001553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3839002283801743872016565 359906464106413488001553)
                    ·
                      rfl

theorem cell22_1051373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 3, 2, 1, 5].length) (baseStart_1051373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051373 prefixEnd_1051373 := by exact prefixLift 1051373
  have htrace : WordTrace (prefixWord ++ tailWord_1051373) baseStart_1051373 baseEnd_1051373 := by
    simpa [prefixWord, tailWord_1051373, baseEnd_1051373] using wordTrace_append hprefix tailTrace_1051373
  have hstable : (prefixWord ++ tailWord_1051373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051373).length < 2 ^ (prefixWord ++ tailWord_1051373).sum := by decide
  have hdescent : baseEnd_1051373 < baseStart_1051373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051388 : List Nat := [2, 2, 2, 1, 3, 2, 2, 2, 2, 4]
def baseStart_1051388 : Nat := 118140960795 + 1051388 * 2 ^ 59
def prefixEnd_1051388 : Nat := 4983230072969 + 3 ^ 40 * 1051388 * 2
def baseEnd_1051388 : Nat := 359911598912958448876507

theorem tailTrace_1051388 : CollatzResearch.WordTrace tailWord_1051388 prefixEnd_1051388 359911598912958448876507 := by
  unfold tailWord_1051388
  simp only [CollatzResearch.WordTrace]
  refine ⟨19173635357504156809893409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25564847143338875746524545 19173635357504156809893409)
  ·
    refine ⟨14380226518128117607420057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19173635357504156809893409 14380226518128117607420057)
    ·
      refine ⟨10785169888596088205565043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14380226518128117607420057 10785169888596088205565043)
      ·
        refine ⟨16177754832894132308347565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10785169888596088205565043 16177754832894132308347565)
        ·
          refine ⟨6066658062335299615630337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16177754832894132308347565 6066658062335299615630337)
          ·
            refine ⟨4549993546751474711722753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6066658062335299615630337 4549993546751474711722753)
            ·
              refine ⟨3412495160063606033792065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4549993546751474711722753 3412495160063606033792065)
              ·
                refine ⟨2559371370047704525344049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3412495160063606033792065 2559371370047704525344049)
                ·
                  refine ⟨1919528527535778394008037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2559371370047704525344049 1919528527535778394008037)
                  ·
                    refine ⟨359911598912958448876507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1919528527535778394008037 359911598912958448876507)
                    ·
                      rfl

theorem cell22_1051388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_1051388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051388 prefixEnd_1051388 := by exact prefixLift 1051388
  have htrace : WordTrace (prefixWord ++ tailWord_1051388) baseStart_1051388 baseEnd_1051388 := by
    simpa [prefixWord, tailWord_1051388, baseEnd_1051388] using wordTrace_append hprefix tailTrace_1051388
  have hstable : (prefixWord ++ tailWord_1051388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051388).length < 2 ^ (prefixWord ++ tailWord_1051388).sum := by decide
  have hdescent : baseEnd_1051388 < baseStart_1051388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051416 : List Nat := [2, 1, 2, 3, 1, 1, 1, 1, 4, 6]
def baseStart_1051416 : Nat := 118140960795 + 1051416 * 2 ^ 59
def prefixEnd_1051416 : Nat := 4983230072969 + 3 ^ 40 * 1051416 * 2
def baseEnd_1051416 : Nat := 359921183885175709176421

theorem tailTrace_1051416 : CollatzResearch.WordTrace tailWord_1051416 prefixEnd_1051416 359921183885175709176421 := by
  unfold tailWord_1051416
  simp only [CollatzResearch.WordTrace]
  refine ⟨19174145979453437200903051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25565527972604582934537401 19174145979453437200903051)
  ·
    refine ⟨28761218969180155801354577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19174145979453437200903051 28761218969180155801354577)
    ·
      refine ⟨21570914226885116851015933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28761218969180155801354577 21570914226885116851015933)
      ·
        refine ⟨8089092835081918819130975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21570914226885116851015933 8089092835081918819130975)
        ·
          refine ⟨12133639252622878228696463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8089092835081918819130975 12133639252622878228696463)
          ·
            refine ⟨18200458878934317343044695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12133639252622878228696463 18200458878934317343044695)
            ·
              refine ⟨27300688318401476014567043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18200458878934317343044695 27300688318401476014567043)
              ·
                refine ⟨40951032477602214021850565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27300688318401476014567043 40951032477602214021850565)
                ·
                  refine ⟨7678318589550415129096981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40951032477602214021850565 7678318589550415129096981)
                  ·
                    refine ⟨359921183885175709176421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7678318589550415129096981 359921183885175709176421)
                    ·
                      rfl

theorem cell22_1051416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 1, 1, 4, 6].length) (baseStart_1051416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051416 prefixEnd_1051416 := by exact prefixLift 1051416
  have htrace : WordTrace (prefixWord ++ tailWord_1051416) baseStart_1051416 baseEnd_1051416 := by
    simpa [prefixWord, tailWord_1051416, baseEnd_1051416] using wordTrace_append hprefix tailTrace_1051416
  have hstable : (prefixWord ++ tailWord_1051416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051416).length < 2 ^ (prefixWord ++ tailWord_1051416).sum := by decide
  have hdescent : baseEnd_1051416 < baseStart_1051416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051435 : List Nat := [1, 1, 1, 1, 2, 1, 2, 9, 1, 3]
def baseStart_1051435 : Nat := 118140960795 + 1051435 * 2 ^ 59
def prefixEnd_1051435 : Nat := 4983230072969 + 3 ^ 40 * 1051435 * 2
def baseEnd_1051435 : Nat := 359927687973465992951363

theorem tailTrace_1051435 : CollatzResearch.WordTrace tailWord_1051435 prefixEnd_1051435 359927687973465992951363 := by
  unfold tailWord_1051435
  simp only [CollatzResearch.WordTrace]
  refine ⟨38348984945838040646747759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25565989963892027097831839 38348984945838040646747759)
  ·
    refine ⟨57523477418757060970121639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38348984945838040646747759 57523477418757060970121639)
    ·
      refine ⟨86285216128135591455182459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57523477418757060970121639 86285216128135591455182459)
      ·
        refine ⟨129427824192203387182773689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86285216128135591455182459 129427824192203387182773689)
        ·
          refine ⟨97070868144152540387080267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129427824192203387182773689 97070868144152540387080267)
          ·
            refine ⟨145606302216228810580620401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97070868144152540387080267 145606302216228810580620401)
            ·
              refine ⟨109204726662171607935465301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145606302216228810580620401 109204726662171607935465301)
              ·
                refine ⟨639871445286161765246867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 109204726662171607935465301 639871445286161765246867)
                ·
                  refine ⟨959807167929242647870301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639871445286161765246867 959807167929242647870301)
                  ·
                    refine ⟨359927687973465992951363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959807167929242647870301 359927687973465992951363)
                    ·
                      rfl

theorem cell22_1051435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 2, 9, 1, 3].length) (baseStart_1051435 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051435 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051435 prefixEnd_1051435 := by exact prefixLift 1051435
  have htrace : WordTrace (prefixWord ++ tailWord_1051435) baseStart_1051435 baseEnd_1051435 := by
    simpa [prefixWord, tailWord_1051435, baseEnd_1051435] using wordTrace_append hprefix tailTrace_1051435
  have hstable : (prefixWord ++ tailWord_1051435).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051435).length < 2 ^ (prefixWord ++ tailWord_1051435).sum := by decide
  have hdescent : baseEnd_1051435 < baseStart_1051435 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051461 : List Nat := [1, 3, 1, 1, 1, 2, 2, 1, 2, 8]
def baseStart_1051461 : Nat := 118140960795 + 1051461 * 2 ^ 59
def prefixEnd_1051461 : Nat := 4983230072969 + 3 ^ 40 * 1051461 * 2
def baseEnd_1051461 : Nat := 359936588304810591801283

theorem tailTrace_1051461 : CollatzResearch.WordTrace tailWord_1051461 prefixEnd_1051461 359936588304810591801283 := by
  unfold tailWord_1051461
  simp only [CollatzResearch.WordTrace]
  refine ⟨38349933243743847087194237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25566622162495898058129491 38349933243743847087194237)
  ·
    refine ⟨14381224966403942657697839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38349933243743847087194237 14381224966403942657697839)
    ·
      refine ⟨21571837449605913986546759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14381224966403942657697839 21571837449605913986546759)
      ·
        refine ⟨32357756174408870979820139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21571837449605913986546759 32357756174408870979820139)
        ·
          refine ⟨48536634261613306469730209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32357756174408870979820139 48536634261613306469730209)
          ·
            refine ⟨36402475696209979852297657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48536634261613306469730209 36402475696209979852297657)
            ·
              refine ⟨27301856772157484889223243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36402475696209979852297657 27301856772157484889223243)
              ·
                refine ⟨40952785158236227333834865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27301856772157484889223243 40952785158236227333834865)
                ·
                  refine ⟨30714588868677170500376149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40952785158236227333834865 30714588868677170500376149)
                  ·
                    refine ⟨359936588304810591801283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30714588868677170500376149 359936588304810591801283)
                    ·
                      rfl

theorem cell22_1051461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 2, 1, 2, 8].length) (baseStart_1051461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051461 prefixEnd_1051461 := by exact prefixLift 1051461
  have htrace : WordTrace (prefixWord ++ tailWord_1051461) baseStart_1051461 baseEnd_1051461 := by
    simpa [prefixWord, tailWord_1051461, baseEnd_1051461] using wordTrace_append hprefix tailTrace_1051461
  have hstable : (prefixWord ++ tailWord_1051461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051461).length < 2 ^ (prefixWord ++ tailWord_1051461).sum := by decide
  have hdescent : baseEnd_1051461 < baseStart_1051461 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051465 : List Nat := [1, 2, 1, 1, 2, 6, 3, 1, 5]
def baseStart_1051465 : Nat := 118140960795 + 1051465 * 2 ^ 59
def prefixEnd_1051465 : Nat := 4983230072969 + 3 ^ 40 * 1051465 * 2
def baseEnd_1051465 : Nat := 119979319195518638233757

theorem tailTrace_1051465 : CollatzResearch.WordTrace tailWord_1051465 prefixEnd_1051465 119979319195518638233757 := by
  unfold tailWord_1051465
  simp only [CollatzResearch.WordTrace]
  refine ⟨38350079135729355770339849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25566719423819570513559899 38350079135729355770339849)
  ·
    refine ⟨28762559351797016827754887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38350079135729355770339849 28762559351797016827754887)
    ·
      refine ⟨43143839027695525241632331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28762559351797016827754887 43143839027695525241632331)
      ·
        refine ⟨64715758541543287862448497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43143839027695525241632331 64715758541543287862448497)
        ·
          refine ⟨48536818906157465896836373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64715758541543287862448497 48536818906157465896836373)
          ·
            refine ⟨2275163386226131213914205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48536818906157465896836373 2275163386226131213914205)
            ·
              refine ⟨853186269834799205217827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2275163386226131213914205 853186269834799205217827)
              ·
                refine ⟨1279779404752198807826741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853186269834799205217827 1279779404752198807826741)
                ·
                  refine ⟨119979319195518638233757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1279779404752198807826741 119979319195518638233757)
                  ·
                    rfl

theorem cell22_1051465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 3, 1, 5].length) (baseStart_1051465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051465 prefixEnd_1051465 := by exact prefixLift 1051465
  have htrace : WordTrace (prefixWord ++ tailWord_1051465) baseStart_1051465 baseEnd_1051465 := by
    simpa [prefixWord, tailWord_1051465, baseEnd_1051465] using wordTrace_append hprefix tailTrace_1051465
  have hstable : (prefixWord ++ tailWord_1051465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051465).length < 2 ^ (prefixWord ++ tailWord_1051465).sum := by decide
  have hdescent : baseEnd_1051465 < baseStart_1051465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051495 : List Nat := [1, 1, 5, 1, 2, 2, 2, 3, 1, 4]
def baseStart_1051495 : Nat := 118140960795 + 1051495 * 2 ^ 59
def prefixEnd_1051495 : Nat := 4983230072969 + 3 ^ 40 * 1051495 * 2
def baseEnd_1051495 : Nat := 359948227199645836451179

theorem tailTrace_1051495 : CollatzResearch.WordTrace tailWord_1051495 prefixEnd_1051495 359948227199645836451179 := by
  unfold tailWord_1051495
  simp only [CollatzResearch.WordTrace]
  refine ⟨38351173325620670893931939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25567448883747113929287959 38351173325620670893931939)
  ·
    refine ⟨57526759988431006340897909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38351173325620670893931939 57526759988431006340897909)
    ·
      refine ⟨5393133748915406844459179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57526759988431006340897909 5393133748915406844459179)
      ·
        refine ⟨8089700623373110266688769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5393133748915406844459179 8089700623373110266688769)
        ·
          refine ⟨6067275467529832700016577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8089700623373110266688769 6067275467529832700016577)
          ·
            refine ⟨4550456600647374525012433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6067275467529832700016577 4550456600647374525012433)
            ·
              refine ⟨3412842450485530893759325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4550456600647374525012433 3412842450485530893759325)
              ·
                refine ⟨1279815918932074085159747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3412842450485530893759325 1279815918932074085159747)
                ·
                  refine ⟨1919723878398111127739621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1279815918932074085159747 1919723878398111127739621)
                  ·
                    refine ⟨359948227199645836451179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1919723878398111127739621 359948227199645836451179)
                    ·
                      rfl

theorem cell22_1051495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 3, 1, 4].length) (baseStart_1051495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051495 prefixEnd_1051495 := by exact prefixLift 1051495
  have htrace : WordTrace (prefixWord ++ tailWord_1051495) baseStart_1051495 baseEnd_1051495 := by
    simpa [prefixWord, tailWord_1051495, baseEnd_1051495] using wordTrace_append hprefix tailTrace_1051495
  have hstable : (prefixWord ++ tailWord_1051495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051495).length < 2 ^ (prefixWord ++ tailWord_1051495).sum := by decide
  have hdescent : baseEnd_1051495 < baseStart_1051495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051523 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 4, 4]
def baseStart_1051523 : Nat := 118140960795 + 1051523 * 2 ^ 59
def prefixEnd_1051523 : Nat := 4983230072969 + 3 ^ 40 * 1051523 * 2
def baseEnd_1051523 : Nat := 359957812171863096751093

theorem tailTrace_1051523 : CollatzResearch.WordTrace tailWord_1051523 prefixEnd_1051523 359957812171863096751093 := by
  unfold tailWord_1051523
  simp only [CollatzResearch.WordTrace]
  refine ⟨38352194569519231675951223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25568129713012821117300815 38352194569519231675951223)
  ·
    refine ⟨57528291854278847513926835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38352194569519231675951223 57528291854278847513926835)
    ·
      refine ⟨86292437781418271270890253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57528291854278847513926835 86292437781418271270890253)
      ·
        refine ⟨32359664168031851726583845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86292437781418271270890253 32359664168031851726583845)
        ·
          refine ⟨6067437031505972198734471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32359664168031851726583845 6067437031505972198734471)
          ·
            refine ⟨9101155547258958298101707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6067437031505972198734471 9101155547258958298101707)
            ·
              refine ⟨13651733320888437447152561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9101155547258958298101707 13651733320888437447152561)
              ·
                refine ⟨10238799990666328085364421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13651733320888437447152561 10238799990666328085364421)
                ·
                  refine ⟨1919774998249936516005829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10238799990666328085364421 1919774998249936516005829)
                  ·
                    refine ⟨359957812171863096751093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1919774998249936516005829 359957812171863096751093)
                    ·
                      rfl

theorem cell22_1051523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 4, 4].length) (baseStart_1051523 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051523 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051523 prefixEnd_1051523 := by exact prefixLift 1051523
  have htrace : WordTrace (prefixWord ++ tailWord_1051523) baseStart_1051523 baseEnd_1051523 := by
    simpa [prefixWord, tailWord_1051523, baseEnd_1051523] using wordTrace_append hprefix tailTrace_1051523
  have hstable : (prefixWord ++ tailWord_1051523).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051523).length < 2 ^ (prefixWord ++ tailWord_1051523).sum := by decide
  have hdescent : baseEnd_1051523 < baseStart_1051523 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051559 : List Nat := [1, 1, 6, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1051559 : Nat := 118140960795 + 1051559 * 2 ^ 59
def prefixEnd_1051559 : Nat := 4983230072969 + 3 ^ 40 * 1051559 * 2
def baseEnd_1051559 : Nat := 359970135707571002850983

theorem tailTrace_1051559 : CollatzResearch.WordTrace tailWord_1051559 prefixEnd_1051559 359970135707571002850983 := by
  unfold tailWord_1051559
  simp only [CollatzResearch.WordTrace]
  refine ⟨38353507597388809824261731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25569005064925873216174487 38353507597388809824261731)
  ·
    refine ⟨57530261396083214736392597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38353507597388809824261731 57530261396083214736392597)
    ·
      refine ⟨2696731002941400690768403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57530261396083214736392597 2696731002941400690768403)
      ·
        refine ⟨4045096504412101036152605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2696731002941400690768403 4045096504412101036152605)
        ·
          refine ⟨1516911189154537888557227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4045096504412101036152605 1516911189154537888557227)
          ·
            refine ⟨2275366783731806832835841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1516911189154537888557227 2275366783731806832835841)
            ·
              refine ⟨1706525087798855124626881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2275366783731806832835841 1706525087798855124626881)
              ·
                refine ⟨1279893815849141343470161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1706525087798855124626881 1279893815849141343470161)
                ·
                  refine ⟨959920361886856007602621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1279893815849141343470161 959920361886856007602621)
                  ·
                    refine ⟨359970135707571002850983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959920361886856007602621 359970135707571002850983)
                    ·
                      rfl

theorem cell22_1051559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1051559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051559 prefixEnd_1051559 := by exact prefixLift 1051559
  have htrace : WordTrace (prefixWord ++ tailWord_1051559) baseStart_1051559 baseEnd_1051559 := by
    simpa [prefixWord, tailWord_1051559, baseEnd_1051559] using wordTrace_append hprefix tailTrace_1051559
  have hstable : (prefixWord ++ tailWord_1051559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051559).length < 2 ^ (prefixWord ++ tailWord_1051559).sum := by decide
  have hdescent : baseEnd_1051559 < baseStart_1051559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051572 : List Nat := [2, 5, 2, 1, 1, 1, 3, 7]
def baseStart_1051572 : Nat := 118140960795 + 1051572 * 2 ^ 59
def prefixEnd_1051572 : Nat := 4983230072969 + 3 ^ 40 * 1051572 * 2
def baseEnd_1051572 : Nat := 39997176208138144697327

theorem tailTrace_1051572 : CollatzResearch.WordTrace tailWord_1051572 prefixEnd_1051572 39997176208138144697327 := by
  unfold tailWord_1051572
  simp only [CollatzResearch.WordTrace]
  refine ⟨19176990873170856522242485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25569321164227808696323313 19176990873170856522242485)
  ·
    refine ⟨1797842894359767798960233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19176990873170856522242485 1797842894359767798960233)
    ·
      refine ⟨1348382170769825849220175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1797842894359767798960233 1348382170769825849220175)
      ·
        refine ⟨2022573256154738773830263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348382170769825849220175 2022573256154738773830263)
        ·
          refine ⟨3033859884232108160745395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2022573256154738773830263 3033859884232108160745395)
          ·
            refine ⟨4550789826348162241118093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3033859884232108160745395 4550789826348162241118093)
            ·
              refine ⟨1706546184880560840419285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4550789826348162241118093 1706546184880560840419285)
              ·
                refine ⟨39997176208138144697327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1706546184880560840419285 39997176208138144697327)
                ·
                  rfl

theorem cell22_1051572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 7].length) (baseStart_1051572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051572 prefixEnd_1051572 := by exact prefixLift 1051572
  have htrace : WordTrace (prefixWord ++ tailWord_1051572) baseStart_1051572 baseEnd_1051572 := by
    simpa [prefixWord, tailWord_1051572, baseEnd_1051572] using wordTrace_append hprefix tailTrace_1051572
  have hstable : (prefixWord ++ tailWord_1051572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051572).length < 2 ^ (prefixWord ++ tailWord_1051572).sum := by decide
  have hdescent : baseEnd_1051572 < baseStart_1051572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051604 : List Nat := [2, 4, 1, 2, 1, 2, 1, 5, 1, 3]
def baseStart_1051604 : Nat := 118140960795 + 1051604 * 2 ^ 59
def prefixEnd_1051604 : Nat := 4983230072969 + 3 ^ 40 * 1051604 * 2
def baseEnd_1051604 : Nat := 359985540127205885475845

theorem tailTrace_1051604 : CollatzResearch.WordTrace tailWord_1051604 prefixEnd_1051604 359985540127205885475845 := by
  unfold tailWord_1051604
  simp only [CollatzResearch.WordTrace]
  refine ⟨19177574441112891254824933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25570099254817188339766577 19177574441112891254824933)
  ·
    refine ⟨3595795207708667110279675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19177574441112891254824933 3595795207708667110279675)
    ·
      refine ⟨5393692811563000665419513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3595795207708667110279675 5393692811563000665419513)
      ·
        refine ⟨4045269608672250499064635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5393692811563000665419513 4045269608672250499064635)
        ·
          refine ⟨6067904413008375748596953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045269608672250499064635 6067904413008375748596953)
          ·
            refine ⟨4550928309756281811447715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6067904413008375748596953 4550928309756281811447715)
            ·
              refine ⟨6826392464634422717171573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4550928309756281811447715 6826392464634422717171573)
              ·
                refine ⟨639974293559477129734835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6826392464634422717171573 639974293559477129734835)
                ·
                  refine ⟨959961440339215694602253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 639974293559477129734835 959961440339215694602253)
                  ·
                    refine ⟨359985540127205885475845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 959961440339215694602253 359985540127205885475845)
                    ·
                      rfl

theorem cell22_1051604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 5, 1, 3].length) (baseStart_1051604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051604 prefixEnd_1051604 := by exact prefixLift 1051604
  have htrace : WordTrace (prefixWord ++ tailWord_1051604) baseStart_1051604 baseEnd_1051604 := by
    simpa [prefixWord, tailWord_1051604, baseEnd_1051604] using wordTrace_append hprefix tailTrace_1051604
  have hstable : (prefixWord ++ tailWord_1051604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051604).length < 2 ^ (prefixWord ++ tailWord_1051604).sum := by decide
  have hdescent : baseEnd_1051604 < baseStart_1051604 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051673 : List Nat := [1, 2, 1, 2, 1, 1, 14]
def baseStart_1051673 : Nat := 118140960795 + 1051673 * 2 ^ 59
def prefixEnd_1051673 : Nat := 4983230072969 + 3 ^ 40 * 1051673 * 2
def baseEnd_1051673 : Nat := 13333672601381952055579

theorem tailTrace_1051673 : CollatzResearch.WordTrace tailWord_1051673 prefixEnd_1051673 13333672601381952055579 := by
  unfold tailWord_1051673
  simp only [CollatzResearch.WordTrace]
  refine ⟨38357665518975807293911673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25571777012650538195941115 38357665518975807293911673)
  ·
    refine ⟨28768249139231855470433755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38357665518975807293911673 28768249139231855470433755)
    ·
      refine ⟨43152373708847783205650633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28768249139231855470433755 43152373708847783205650633)
      ·
        refine ⟨32364280281635837404237975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43152373708847783205650633 32364280281635837404237975)
        ·
          refine ⟨48546420422453756106356963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32364280281635837404237975 48546420422453756106356963)
          ·
            refine ⟨72819630633680634159535445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48546420422453756106356963 72819630633680634159535445)
            ·
              refine ⟨13333672601381952055579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 72819630633680634159535445 13333672601381952055579)
              ·
                rfl

theorem cell22_1051673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 14].length) (baseStart_1051673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051673 prefixEnd_1051673 := by exact prefixLift 1051673
  have htrace : WordTrace (prefixWord ++ tailWord_1051673) baseStart_1051673 baseEnd_1051673 := by
    simpa [prefixWord, tailWord_1051673, baseEnd_1051673] using wordTrace_append hprefix tailTrace_1051673
  have hstable : (prefixWord ++ tailWord_1051673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051673).length < 2 ^ (prefixWord ++ tailWord_1051673).sum := by decide
  have hdescent : baseEnd_1051673 < baseStart_1051673 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051679 : List Nat := [1, 1, 2, 4, 1, 4, 3, 2, 4]
def baseStart_1051679 : Nat := 118140960795 + 1051679 * 2 ^ 59
def prefixEnd_1051679 : Nat := 4983230072969 + 3 ^ 40 * 1051679 * 2
def baseEnd_1051679 : Nat := 120003738053310229950205

theorem tailTrace_1051679 : CollatzResearch.WordTrace tailWord_1051679 prefixEnd_1051679 120003738053310229950205 := by
  unfold tailWord_1051679
  simp only [CollatzResearch.WordTrace]
  refine ⟨38357884356954070318630091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25571922904636046879086727 38357884356954070318630091)
  ·
    refine ⟨57536826535431105477945137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38357884356954070318630091 57536826535431105477945137)
    ·
      refine ⟨43152619901573329108458853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57536826535431105477945137 43152619901573329108458853)
      ·
        refine ⟨8091116231544999207836035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43152619901573329108458853 8091116231544999207836035)
        ·
          refine ⟨12136674347317498811754053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8091116231544999207836035 12136674347317498811754053)
          ·
            refine ⟨2275626440122031027203885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12136674347317498811754053 2275626440122031027203885)
            ·
              refine ⟨853359915045761635201457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2275626440122031027203885 853359915045761635201457)
              ·
                refine ⟨640019936284321226401093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853359915045761635201457 640019936284321226401093)
                ·
                  refine ⟨120003738053310229950205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640019936284321226401093 120003738053310229950205)
                  ·
                    rfl

theorem cell22_1051679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 4, 3, 2, 4].length) (baseStart_1051679 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051679 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051679 prefixEnd_1051679 := by exact prefixLift 1051679
  have htrace : WordTrace (prefixWord ++ tailWord_1051679) baseStart_1051679 baseEnd_1051679 := by
    simpa [prefixWord, tailWord_1051679, baseEnd_1051679] using wordTrace_append hprefix tailTrace_1051679
  have hstable : (prefixWord ++ tailWord_1051679).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051679).length < 2 ^ (prefixWord ++ tailWord_1051679).sum := by decide
  have hdescent : baseEnd_1051679 < baseStart_1051679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051694 : List Nat := [4, 1, 3, 1, 1, 1, 3, 3, 2, 3]
def baseStart_1051694 : Nat := 118140960795 + 1051694 * 2 ^ 59
def prefixEnd_1051694 : Nat := 4983230072969 + 3 ^ 40 * 1051694 * 2
def baseEnd_1051694 : Nat := 360016348966475650725569

theorem tailTrace_1051694 : CollatzResearch.WordTrace tailWord_1051694 prefixEnd_1051694 360016348966475650725569 := by
  unfold tailWord_1051694
  simp only [CollatzResearch.WordTrace]
  refine ⟨4794803931487465985053267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25572287634599818586950757 4794803931487465985053267)
  ·
    refine ⟨7192205897231198977579901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4794803931487465985053267 7192205897231198977579901)
    ·
      refine ⟨2697077211461699616592463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7192205897231198977579901 2697077211461699616592463)
      ·
        refine ⟨4045615817192549424888695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2697077211461699616592463 4045615817192549424888695)
        ·
          refine ⟨6068423725788824137333043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4045615817192549424888695 6068423725788824137333043)
          ·
            refine ⟨9102635588683236205999565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6068423725788824137333043 9102635588683236205999565)
            ·
              refine ⟨3413488345756213577249837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9102635588683236205999565 3413488345756213577249837)
              ·
                refine ⟨1280058129658580091468689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3413488345756213577249837 1280058129658580091468689)
                ·
                  refine ⟨960043597243935068601517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280058129658580091468689 960043597243935068601517)
                  ·
                    refine ⟨360016348966475650725569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960043597243935068601517 360016348966475650725569)
                    ·
                      rfl

theorem cell22_1051694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 3, 2, 3].length) (baseStart_1051694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051694 prefixEnd_1051694 := by exact prefixLift 1051694
  have htrace : WordTrace (prefixWord ++ tailWord_1051694) baseStart_1051694 baseEnd_1051694 := by
    simpa [prefixWord, tailWord_1051694, baseEnd_1051694] using wordTrace_append hprefix tailTrace_1051694
  have hstable : (prefixWord ++ tailWord_1051694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051694).length < 2 ^ (prefixWord ++ tailWord_1051694).sum := by decide
  have hdescent : baseEnd_1051694 < baseStart_1051694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051741 : List Nat := [1, 4, 4, 1, 3, 1, 1, 7]
def baseStart_1051741 : Nat := 118140960795 + 1051741 * 2 ^ 59
def prefixEnd_1051741 : Nat := 4983230072969 + 3 ^ 40 * 1051741 * 2
def baseEnd_1051741 : Nat := 40003604225220354977825

theorem tailTrace_1051741 : CollatzResearch.WordTrace tailWord_1051741 prefixEnd_1051741 40003604225220354977825 := by
  unfold tailWord_1051741
  simp only [CollatzResearch.WordTrace]
  refine ⟨38360145682729454907387077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25573430455152969938258051 38360145682729454907387077)
  ·
    refine ⟨7192527315511772795135077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38360145682729454907387077 7192527315511772795135077)
    ·
      refine ⟨1348598871658457399087827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7192527315511772795135077 1348598871658457399087827)
      ·
        refine ⟨2022898307487686098631741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1348598871658457399087827 2022898307487686098631741)
        ·
          refine ⟨758586865307882286986903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2022898307487686098631741 758586865307882286986903)
          ·
            refine ⟨1137880297961823430480355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758586865307882286986903 1137880297961823430480355)
            ·
              refine ⟨1706820446942735145720533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1137880297961823430480355 1706820446942735145720533)
              ·
                refine ⟨40003604225220354977825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1706820446942735145720533 40003604225220354977825)
                ·
                  rfl

theorem cell22_1051741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 3, 1, 1, 7].length) (baseStart_1051741 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051741 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051741 prefixEnd_1051741 := by exact prefixLift 1051741
  have htrace : WordTrace (prefixWord ++ tailWord_1051741) baseStart_1051741 baseEnd_1051741 := by
    simpa [prefixWord, tailWord_1051741, baseEnd_1051741] using wordTrace_append hprefix tailTrace_1051741
  have hstable : (prefixWord ++ tailWord_1051741).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051741).length < 2 ^ (prefixWord ++ tailWord_1051741).sum := by decide
  have hdescent : baseEnd_1051741 < baseStart_1051741 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051795 : List Nat := [1, 1, 1, 2, 1, 2, 4, 2, 3, 5]
def baseStart_1051795 : Nat := 118140960795 + 1051795 * 2 ^ 59
def prefixEnd_1051795 : Nat := 4983230072969 + 3 ^ 40 * 1051795 * 2
def baseEnd_1051795 : Nat := 360050923330545053950259

theorem tailTrace_1051795 : CollatzResearch.WordTrace tailWord_1051795 prefixEnd_1051795 360050923330545053950259 := by
  unfold tailWord_1051795
  simp only [CollatzResearch.WordTrace]
  refine ⟨38362115224533822129852839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25574743483022548086568559 38362115224533822129852839)
  ·
    refine ⟨57543172836800733194779259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38362115224533822129852839 57543172836800733194779259)
    ·
      refine ⟨86314759255201099792168889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57543172836800733194779259 86314759255201099792168889)
      ·
        refine ⟨64736069441400824844126667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86314759255201099792168889 64736069441400824844126667)
        ·
          refine ⟨97104104162101237266190001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64736069441400824844126667 97104104162101237266190001)
          ·
            refine ⟨72828078121575927949642501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97104104162101237266190001 72828078121575927949642501)
            ·
              refine ⟨13655264647795486490557969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72828078121575927949642501 13655264647795486490557969)
              ·
                refine ⟨10241448485846614867918477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13655264647795486490557969 10241448485846614867918477)
                ·
                  refine ⟨3840543182192480575469429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10241448485846614867918477 3840543182192480575469429)
                  ·
                    refine ⟨360050923330545053950259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3840543182192480575469429 360050923330545053950259)
                    ·
                      rfl

theorem cell22_1051795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 4, 2, 3, 5].length) (baseStart_1051795 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051795 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051795 prefixEnd_1051795 := by exact prefixLift 1051795
  have htrace : WordTrace (prefixWord ++ tailWord_1051795) baseStart_1051795 baseEnd_1051795 := by
    simpa [prefixWord, tailWord_1051795, baseEnd_1051795] using wordTrace_append hprefix tailTrace_1051795
  have hstable : (prefixWord ++ tailWord_1051795).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051795).length < 2 ^ (prefixWord ++ tailWord_1051795).sum := by decide
  have hdescent : baseEnd_1051795 < baseStart_1051795 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051908 : List Nat := [2, 3, 2, 2, 2, 2, 1, 4, 1, 3]
def baseStart_1051908 : Nat := 118140960795 + 1051908 * 2 ^ 59
def prefixEnd_1051908 : Nat := 4983230072969 + 3 ^ 40 * 1051908 * 2
def baseEnd_1051908 : Nat := 360089605539850425874913

theorem tailTrace_1051908 : CollatzResearch.WordTrace tailWord_1051908 prefixEnd_1051908 360089605539850425874913 := by
  unfold tailWord_1051908
  simp only [CollatzResearch.WordTrace]
  refine ⟨19183118336562221214358189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25577491115416294952477585 19183118336562221214358189)
  ·
    refine ⟨7193669376210832955384321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19183118336562221214358189 7193669376210832955384321)
    ·
      refine ⟨5395252032158124716538241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7193669376210832955384321 5395252032158124716538241)
      ·
        refine ⟨4046439024118593537403681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5395252032158124716538241 4046439024118593537403681)
        ·
          refine ⟨3034829268088945153052761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4046439024118593537403681 3034829268088945153052761)
          ·
            refine ⟨2276121951066708864789571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3034829268088945153052761 2276121951066708864789571)
            ·
              refine ⟨3414182926600063297184357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276121951066708864789571 3414182926600063297184357)
              ·
                refine ⟨640159298737511868222067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3414182926600063297184357 640159298737511868222067)
                ·
                  refine ⟨960238948106267802333101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640159298737511868222067 960238948106267802333101)
                  ·
                    refine ⟨360089605539850425874913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960238948106267802333101 360089605539850425874913)
                    ·
                      rfl

theorem cell22_1051908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 2, 1, 4, 1, 3].length) (baseStart_1051908 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051908 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051908 prefixEnd_1051908 := by exact prefixLift 1051908
  have htrace : WordTrace (prefixWord ++ tailWord_1051908) baseStart_1051908 baseEnd_1051908 := by
    simpa [prefixWord, tailWord_1051908, baseEnd_1051908] using wordTrace_append hprefix tailTrace_1051908
  have hstable : (prefixWord ++ tailWord_1051908).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051908).length < 2 ^ (prefixWord ++ tailWord_1051908).sum := by decide
  have hdescent : baseEnd_1051908 < baseStart_1051908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051932 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 8]
def baseStart_1051932 : Nat := 118140960795 + 1051932 * 2 ^ 59
def prefixEnd_1051932 : Nat := 4983230072969 + 3 ^ 40 * 1051932 * 2
def baseEnd_1051932 : Nat := 120032607076774121091613

theorem tailTrace_1051932 : CollatzResearch.WordTrace tailWord_1051932 prefixEnd_1051932 120032607076774121091613 := by
  unfold tailWord_1051932
  simp only [CollatzResearch.WordTrace]
  refine ⟨19183556012518747263795025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25578074683358329685060033 19183556012518747263795025)
  ·
    refine ⟨14387667009389060447846269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19183556012518747263795025 14387667009389060447846269)
    ·
      refine ⟨5395375128520897667942351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14387667009389060447846269 5395375128520897667942351)
      ·
        refine ⟨8093062692781346501913527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5395375128520897667942351 8093062692781346501913527)
        ·
          refine ⟨12139594039172019752870291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8093062692781346501913527 12139594039172019752870291)
          ·
            refine ⟨18209391058758029629305437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12139594039172019752870291 18209391058758029629305437)
            ·
              refine ⟨6828521647034261110989539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18209391058758029629305437 6828521647034261110989539)
              ·
                refine ⟨10242782470551391666484309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6828521647034261110989539 10242782470551391666484309)
                ·
                  refine ⟨120032607076774121091613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10242782470551391666484309 120032607076774121091613)
                  ·
                    rfl

theorem cell22_1051932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 8].length) (baseStart_1051932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051932 prefixEnd_1051932 := by exact prefixLift 1051932
  have htrace : WordTrace (prefixWord ++ tailWord_1051932) baseStart_1051932 baseEnd_1051932 := by
    simpa [prefixWord, tailWord_1051932, baseEnd_1051932] using wordTrace_append hprefix tailTrace_1051932
  have hstable : (prefixWord ++ tailWord_1051932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051932).length < 2 ^ (prefixWord ++ tailWord_1051932).sum := by decide
  have hdescent : baseEnd_1051932 < baseStart_1051932 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051966 : List Nat := [4, 2, 1, 2, 1, 1, 1, 6, 4]
def baseStart_1051966 : Nat := 118140960795 + 1051966 * 2 ^ 59
def prefixEnd_1051966 : Nat := 4983230072969 + 3 ^ 40 * 1051966 * 2
def baseEnd_1051966 : Nat := 120036486708385869308245

theorem tailTrace_1051966 : CollatzResearch.WordTrace tailWord_1051966 prefixEnd_1051966 120036486708385869308245 := by
  unfold tailWord_1051966
  simp only [CollatzResearch.WordTrace]
  refine ⟨4796044013364289791790969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25578901404609545556218501 4796044013364289791790969)
  ·
    refine ⟨3597033010023217343843227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4796044013364289791790969 3597033010023217343843227)
    ·
      refine ⟨5395549515034826015764841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3597033010023217343843227 5395549515034826015764841)
      ·
        refine ⟨4046662136276119511823631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5395549515034826015764841 4046662136276119511823631)
        ·
          refine ⟨6069993204414179267735447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4046662136276119511823631 6069993204414179267735447)
          ·
            refine ⟨9104989806621268901603171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6069993204414179267735447 9104989806621268901603171)
            ·
              refine ⟨13657484709931903352404757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9104989806621268901603171 13657484709931903352404757)
              ·
                refine ⟨640194595778057969643973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13657484709931903352404757 640194595778057969643973)
                ·
                  refine ⟨120036486708385869308245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640194595778057969643973 120036486708385869308245)
                  ·
                    rfl

theorem cell22_1051966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 1, 6, 4].length) (baseStart_1051966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051966 prefixEnd_1051966 := by exact prefixLift 1051966
  have htrace : WordTrace (prefixWord ++ tailWord_1051966) baseStart_1051966 baseEnd_1051966 := by
    simpa [prefixWord, tailWord_1051966, baseEnd_1051966] using wordTrace_append hprefix tailTrace_1051966
  have hstable : (prefixWord ++ tailWord_1051966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051966).length < 2 ^ (prefixWord ++ tailWord_1051966).sum := by decide
  have hdescent : baseEnd_1051966 < baseStart_1051966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051992 : List Nat := [2, 1, 2, 2, 1, 1, 3, 1, 2, 7]
def baseStart_1051992 : Nat := 118140960795 + 1051992 * 2 ^ 59
def prefixEnd_1051992 : Nat := 4983230072969 + 3 ^ 40 * 1051992 * 2
def baseEnd_1051992 : Nat := 360118360456502206774655

theorem tailTrace_1051992 : CollatzResearch.WordTrace tailWord_1051992 prefixEnd_1051992 360118360456502206774655 := by
  unfold tailWord_1051992
  simp only [CollatzResearch.WordTrace]
  refine ⟨19184650202410062387387115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25579533603213416516516153 19184650202410062387387115)
  ·
    refine ⟨28776975303615093581080673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19184650202410062387387115 28776975303615093581080673)
    ·
      refine ⟨21582731477711320185810505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28776975303615093581080673 21582731477711320185810505)
      ·
        refine ⟨16187048608283490139357879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21582731477711320185810505 16187048608283490139357879)
        ·
          refine ⟨24280572912425235209036819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16187048608283490139357879 24280572912425235209036819)
          ·
            refine ⟨36420859368637852813555229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24280572912425235209036819 36420859368637852813555229)
            ·
              refine ⟨13657822263239194805083211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36420859368637852813555229 13657822263239194805083211)
              ·
                refine ⟨20486733394858792207624817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13657822263239194805083211 20486733394858792207624817)
                ·
                  refine ⟨15365050046144094155718613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20486733394858792207624817 15365050046144094155718613)
                  ·
                    refine ⟨360118360456502206774655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15365050046144094155718613 360118360456502206774655)
                    ·
                      rfl

theorem cell22_1051992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 3, 1, 2, 7].length) (baseStart_1051992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051992 prefixEnd_1051992 := by exact prefixLift 1051992
  have htrace : WordTrace (prefixWord ++ tailWord_1051992) baseStart_1051992 baseEnd_1051992 := by
    simpa [prefixWord, tailWord_1051992, baseEnd_1051992] using wordTrace_append hprefix tailTrace_1051992
  have hstable : (prefixWord ++ tailWord_1051992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051992).length < 2 ^ (prefixWord ++ tailWord_1051992).sum := by decide
  have hdescent : baseEnd_1051992 < baseStart_1051992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1051994 : List Nat := [3, 1, 1, 2, 1, 2, 6, 6]
def baseStart_1051994 : Nat := 118140960795 + 1051994 * 2 ^ 59
def prefixEnd_1051994 : Nat := 4983230072969 + 3 ^ 40 * 1051994 * 2
def baseEnd_1051994 : Nat := 40013227233041652024961

theorem tailTrace_1051994 : CollatzResearch.WordTrace tailWord_1051994 prefixEnd_1051994 40013227233041652024961 := by
  unfold tailWord_1051994
  simp only [CollatzResearch.WordTrace]
  refine ⟨9592343337703219779086759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25579582233875252744231357 9592343337703219779086759)
  ·
    refine ⟨14388515006554829668630139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9592343337703219779086759 14388515006554829668630139)
    ·
      refine ⟨21582772509832244502945209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14388515006554829668630139 21582772509832244502945209)
      ·
        refine ⟨16187079382374183377208907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21582772509832244502945209 16187079382374183377208907)
        ·
          refine ⟨24280619073561275065813361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16187079382374183377208907 24280619073561275065813361)
          ·
            refine ⟨18210464305170956299360021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24280619073561275065813361 18210464305170956299360021)
            ·
              refine ⟨853615514304888576532501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 18210464305170956299360021 853615514304888576532501)
              ·
                refine ⟨40013227233041652024961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 853615514304888576532501 40013227233041652024961)
                ·
                  rfl

theorem cell22_1051994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 6, 6].length) (baseStart_1051994 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1051994 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1051994 prefixEnd_1051994 := by exact prefixLift 1051994
  have htrace : WordTrace (prefixWord ++ tailWord_1051994) baseStart_1051994 baseEnd_1051994 := by
    simpa [prefixWord, tailWord_1051994, baseEnd_1051994] using wordTrace_append hprefix tailTrace_1051994
  have hstable : (prefixWord ++ tailWord_1051994).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1051994).length < 2 ^ (prefixWord ++ tailWord_1051994).sum := by decide
  have hdescent : baseEnd_1051994 < baseStart_1051994 := by decide
  rcases family_descends (prefixWord ++ tailWord_1051994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052077 : List Nat := [1, 5, 2, 2, 1, 1, 4, 2, 1, 3]
def baseStart_1052077 : Nat := 118140960795 + 1052077 * 2 ^ 59
def prefixEnd_1052077 : Nat := 4983230072969 + 3 ^ 40 * 1052077 * 2
def baseEnd_1052077 : Nat := 360147457693590318399395

theorem tailTrace_1052077 : CollatzResearch.WordTrace tailWord_1052077 prefixEnd_1052077 360147457693590318399395 := by
  unfold tailWord_1052077
  simp only [CollatzResearch.WordTrace]
  refine ⟨38372400609512184291618485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25581600406341456194412323 38372400609512184291618485)
  ·
    refine ⟨3597412557141767277339233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38372400609512184291618485 3597412557141767277339233)
    ·
      refine ⟨2698059417856325458004425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3597412557141767277339233 2698059417856325458004425)
      ·
        refine ⟨2023544563392244093503319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2698059417856325458004425 2023544563392244093503319)
        ·
          refine ⟨3035316845088366140254979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023544563392244093503319 3035316845088366140254979)
          ·
            refine ⟨4552975267632549210382469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3035316845088366140254979 4552975267632549210382469)
            ·
              refine ⟨853682862681102976946713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4552975267632549210382469 853682862681102976946713)
              ·
                refine ⟨640262147010827232710035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 853682862681102976946713 640262147010827232710035)
                ·
                  refine ⟨960393220516240849065053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640262147010827232710035 960393220516240849065053)
                  ·
                    refine ⟨360147457693590318399395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960393220516240849065053 360147457693590318399395)
                    ·
                      rfl

theorem cell22_1052077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 4, 2, 1, 3].length) (baseStart_1052077 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052077 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052077 prefixEnd_1052077 := by exact prefixLift 1052077
  have htrace : WordTrace (prefixWord ++ tailWord_1052077) baseStart_1052077 baseEnd_1052077 := by
    simpa [prefixWord, tailWord_1052077, baseEnd_1052077] using wordTrace_append hprefix tailTrace_1052077
  have hstable : (prefixWord ++ tailWord_1052077).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052077).length < 2 ^ (prefixWord ++ tailWord_1052077).sum := by decide
  have hdescent : baseEnd_1052077 < baseStart_1052077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052099 : List Nat := [1, 1, 1, 3, 1, 1, 5, 3, 1, 5]
def baseStart_1052099 : Nat := 118140960795 + 1052099 * 2 ^ 59
def prefixEnd_1052099 : Nat := 4983230072969 + 3 ^ 40 * 1052099 * 2
def baseEnd_1052099 : Nat := 360154988743189594349327

theorem tailTrace_1052099 : CollatzResearch.WordTrace tailWord_1052099 prefixEnd_1052099 360154988743189594349327 := by
  unfold tailWord_1052099
  simp only [CollatzResearch.WordTrace]
  refine ⟨38373203015432482048919351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25582135343621654699279567 38373203015432482048919351)
  ·
    refine ⟨57559804523148723073379027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38373203015432482048919351 57559804523148723073379027)
    ·
      refine ⟨86339706784723084610068541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57559804523148723073379027 86339706784723084610068541)
      ·
        refine ⟨32377390044271156728775703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86339706784723084610068541 32377390044271156728775703)
        ·
          refine ⟨48566085066406735093163555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32377390044271156728775703 48566085066406735093163555)
          ·
            refine ⟨72849127599610102639745333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48566085066406735093163555 72849127599610102639745333)
            ·
              refine ⟨6829605712463447122476125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 72849127599610102639745333 6829605712463447122476125)
              ·
                refine ⟨2561102142173792670928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6829605712463447122476125 2561102142173792670928547)
                ·
                  refine ⟨3841653213260689006392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2561102142173792670928547 3841653213260689006392821)
                  ·
                    refine ⟨360154988743189594349327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3841653213260689006392821 360154988743189594349327)
                    ·
                      rfl

theorem cell22_1052099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 5, 3, 1, 5].length) (baseStart_1052099 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052099 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052099 prefixEnd_1052099 := by exact prefixLift 1052099
  have htrace : WordTrace (prefixWord ++ tailWord_1052099) baseStart_1052099 baseEnd_1052099 := by
    simpa [prefixWord, tailWord_1052099, baseEnd_1052099] using wordTrace_append hprefix tailTrace_1052099
  have hstable : (prefixWord ++ tailWord_1052099).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052099).length < 2 ^ (prefixWord ++ tailWord_1052099).sum := by decide
  have hdescent : baseEnd_1052099 < baseStart_1052099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052129 : List Nat := [1, 2, 3, 1, 2, 4, 9]
def baseStart_1052129 : Nat := 118140960795 + 1052129 * 2 ^ 59
def prefixEnd_1052129 : Nat := 4983230072969 + 3 ^ 40 * 1052129 * 2
def baseEnd_1052129 : Nat := 13339454013195537633305

theorem tailTrace_1052129 : CollatzResearch.WordTrace tailWord_1052129 prefixEnd_1052129 13339454013195537633305 := by
  unfold tailWord_1052129
  simp only [CollatzResearch.WordTrace]
  refine ⟨38374297205323797172511441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25582864803549198115007627 38374297205323797172511441)
  ·
    refine ⟨28780722903992847879383581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38374297205323797172511441 28780722903992847879383581)
    ·
      refine ⟨10792771088997317954768843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28780722903992847879383581 10792771088997317954768843)
      ·
        refine ⟨16189156633495976932153265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10792771088997317954768843 16189156633495976932153265)
        ·
          refine ⟨12141867475121982699114949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16189156633495976932153265 12141867475121982699114949)
          ·
            refine ⟨2276600151585371756084053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12141867475121982699114949 2276600151585371756084053)
            ·
              refine ⟨13339454013195537633305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2276600151585371756084053 13339454013195537633305)
              ·
                rfl

theorem cell22_1052129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 9].length) (baseStart_1052129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052129 prefixEnd_1052129 := by exact prefixLift 1052129
  have htrace : WordTrace (prefixWord ++ tailWord_1052129) baseStart_1052129 baseEnd_1052129 := by
    simpa [prefixWord, tailWord_1052129, baseEnd_1052129] using wordTrace_append hprefix tailTrace_1052129
  have hstable : (prefixWord ++ tailWord_1052129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052129).length < 2 ^ (prefixWord ++ tailWord_1052129).sum := by decide
  have hdescent : baseEnd_1052129 < baseStart_1052129 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052133 : List Nat := [1, 3, 1, 5, 1, 2, 1, 1, 4, 3]
def baseStart_1052133 : Nat := 118140960795 + 1052133 * 2 ^ 59
def prefixEnd_1052133 : Nat := 4983230072969 + 3 ^ 40 * 1052133 * 2
def baseEnd_1052133 : Nat := 360166627638024838999223

theorem tailTrace_1052133 : CollatzResearch.WordTrace tailWord_1052133 prefixEnd_1052133 360166627638024838999223 := by
  unfold tailWord_1052133
  simp only [CollatzResearch.WordTrace]
  refine ⟨38374443097309305855657053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25582962064872870570438035 38374443097309305855657053)
  ·
    refine ⟨14390416161490989695871395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38374443097309305855657053 14390416161490989695871395)
    ·
      refine ⟨21585624242236484543807093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14390416161490989695871395 21585624242236484543807093)
      ·
        refine ⟨2023652272709670425981915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21585624242236484543807093 2023652272709670425981915)
        ·
          refine ⟨3035478409064505638972873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2023652272709670425981915 3035478409064505638972873)
          ·
            refine ⟨2276608806798379229229655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3035478409064505638972873 2276608806798379229229655)
            ·
              refine ⟨3414913210197568843844483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276608806798379229229655 3414913210197568843844483)
              ·
                refine ⟨5122369815296353265766725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3414913210197568843844483 5122369815296353265766725)
                ·
                  refine ⟨960444340368066237331261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5122369815296353265766725 960444340368066237331261)
                  ·
                    refine ⟨360166627638024838999223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960444340368066237331261 360166627638024838999223)
                    ·
                      rfl

theorem cell22_1052133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 1, 1, 4, 3].length) (baseStart_1052133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052133 prefixEnd_1052133 := by exact prefixLift 1052133
  have htrace : WordTrace (prefixWord ++ tailWord_1052133) baseStart_1052133 baseEnd_1052133 := by
    simpa [prefixWord, tailWord_1052133, baseEnd_1052133] using wordTrace_append hprefix tailTrace_1052133
  have hstable : (prefixWord ++ tailWord_1052133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052133).length < 2 ^ (prefixWord ++ tailWord_1052133).sum := by decide
  have hdescent : baseEnd_1052133 < baseStart_1052133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052180 : List Nat := [2, 4, 3, 1, 3, 1, 8]
def baseStart_1052180 : Nat := 118140960795 + 1052180 * 2 ^ 59
def prefixEnd_1052180 : Nat := 4983230072969 + 3 ^ 40 * 1052180 * 2
def baseEnd_1052180 : Nat := 13340100618464162336077

theorem tailTrace_1052180 : CollatzResearch.WordTrace tailWord_1052180 prefixEnd_1052180 13340100618464162336077 := by
  unfold tailWord_1052180
  simp only [CollatzResearch.WordTrace]
  refine ⟨19188078664069516441308997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25584104885426021921745329 19188078664069516441308997)
  ·
    refine ⟨3597764749513034332745437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19188078664069516441308997 3597764749513034332745437)
    ·
      refine ⟨1349161781067387874779539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3597764749513034332745437 1349161781067387874779539)
      ·
        refine ⟨2023742671601081812169309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349161781067387874779539 2023742671601081812169309)
        ·
          refine ⟨758903501850405679563491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2023742671601081812169309 758903501850405679563491)
          ·
            refine ⟨1138355252775608519345237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 758903501850405679563491 1138355252775608519345237)
            ·
              refine ⟨13340100618464162336077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 1138355252775608519345237 13340100618464162336077)
              ·
                rfl

theorem cell22_1052180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 3, 1, 8].length) (baseStart_1052180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052180 prefixEnd_1052180 := by exact prefixLift 1052180
  have htrace : WordTrace (prefixWord ++ tailWord_1052180) baseStart_1052180 baseEnd_1052180 := by
    simpa [prefixWord, tailWord_1052180, baseEnd_1052180] using wordTrace_append hprefix tailTrace_1052180
  have hstable : (prefixWord ++ tailWord_1052180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052180).length < 2 ^ (prefixWord ++ tailWord_1052180).sum := by decide
  have hdescent : baseEnd_1052180 < baseStart_1052180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052195 : List Nat := [1, 1, 1, 4, 5, 2, 1, 1, 3, 3]
def baseStart_1052195 : Nat := 118140960795 + 1052195 * 2 ^ 59
def prefixEnd_1052195 : Nat := 4983230072969 + 3 ^ 40 * 1052195 * 2
def baseEnd_1052195 : Nat := 360187851505077343949033

theorem tailTrace_1052195 : CollatzResearch.WordTrace tailWord_1052195 prefixEnd_1052195 360187851505077343949033 := by
  unfold tailWord_1052195
  simp only [CollatzResearch.WordTrace]
  refine ⟨38376704423084690444414039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25584469615389793629609359 38376704423084690444414039)
  ·
    refine ⟨57565056634627035666621059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38376704423084690444414039 57565056634627035666621059)
    ·
      refine ⟨86347584951940553499931589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57565056634627035666621059 86347584951940553499931589)
      ·
        refine ⟨16190172178488853781237173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86347584951940553499931589 16190172178488853781237173)
        ·
          refine ⟨1517828641733330041990985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16190172178488853781237173 1517828641733330041990985)
          ·
            refine ⟨1138371481299997531493239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1517828641733330041990985 1138371481299997531493239)
            ·
              refine ⟨1707557221949996297239859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138371481299997531493239 1707557221949996297239859)
              ·
                refine ⟨2561335832924994445859789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707557221949996297239859 2561335832924994445859789)
                ·
                  refine ⟨960500937346872917197421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2561335832924994445859789 960500937346872917197421)
                  ·
                    refine ⟨360187851505077343949033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960500937346872917197421 360187851505077343949033)
                    ·
                      rfl

theorem cell22_1052195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 2, 1, 1, 3, 3].length) (baseStart_1052195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052195 prefixEnd_1052195 := by exact prefixLift 1052195
  have htrace : WordTrace (prefixWord ++ tailWord_1052195) baseStart_1052195 baseEnd_1052195 := by
    simpa [prefixWord, tailWord_1052195, baseEnd_1052195] using wordTrace_append hprefix tailTrace_1052195
  have hstable : (prefixWord ++ tailWord_1052195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052195).length < 2 ^ (prefixWord ++ tailWord_1052195).sum := by decide
  have hdescent : baseEnd_1052195 < baseStart_1052195 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052204 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 1, 10]
def baseStart_1052204 : Nat := 118140960795 + 1052204 * 2 ^ 59
def prefixEnd_1052204 : Nat := 4983230072969 + 3 ^ 40 * 1052204 * 2
def baseEnd_1052204 : Nat := 360190932389004320474005

theorem tailTrace_1052204 : CollatzResearch.WordTrace tailWord_1052204 prefixEnd_1052204 360190932389004320474005 := by
  unfold tailWord_1052204
  simp only [CollatzResearch.WordTrace]
  refine ⟨19188516340026042490745833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25584688453368056654327777 19188516340026042490745833)
  ·
    refine ⟨14391387255019531868059375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19188516340026042490745833 14391387255019531868059375)
    ·
      refine ⟨21587080882529297802089063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14391387255019531868059375 21587080882529297802089063)
      ·
        refine ⟨32380621323793946703133595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21587080882529297802089063 32380621323793946703133595)
        ·
          refine ⟨48570931985690920054700393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32380621323793946703133595 48570931985690920054700393)
          ·
            refine ⟨36428198989268190041025295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48570931985690920054700393 36428198989268190041025295)
            ·
              refine ⟨54642298483902285061537943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36428198989268190041025295 54642298483902285061537943)
              ·
                refine ⟨81963447725853427592306915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54642298483902285061537943 81963447725853427592306915)
                ·
                  refine ⟨122945171588780141388460373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81963447725853427592306915 122945171588780141388460373)
                  ·
                    refine ⟨360190932389004320474005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 122945171588780141388460373 360190932389004320474005)
                    ·
                      rfl

theorem cell22_1052204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 10].length) (baseStart_1052204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052204 prefixEnd_1052204 := by exact prefixLift 1052204
  have htrace : WordTrace (prefixWord ++ tailWord_1052204) baseStart_1052204 baseEnd_1052204 := by
    simpa [prefixWord, tailWord_1052204, baseEnd_1052204] using wordTrace_append hprefix tailTrace_1052204
  have hstable : (prefixWord ++ tailWord_1052204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052204).length < 2 ^ (prefixWord ++ tailWord_1052204).sum := by decide
  have hdescent : baseEnd_1052204 < baseStart_1052204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052246 : List Nat := [5, 2, 2, 2, 1, 1, 1, 4, 1, 3]
def baseStart_1052246 : Nat := 118140960795 + 1052246 * 2 ^ 59
def prefixEnd_1052246 : Nat := 4983230072969 + 3 ^ 40 * 1052246 * 2
def baseEnd_1052246 : Nat := 360205309847330210923877

theorem tailTrace_1052246 : CollatzResearch.WordTrace tailWord_1052246 prefixEnd_1052246 360205309847330210923877 := by
  unfold tailWord_1052246
  simp only [CollatzResearch.WordTrace]
  refine ⟨2398660284118745384657537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25585709697266617436347061 2398660284118745384657537)
  ·
    refine ⟨1798995213089059038493153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2398660284118745384657537 1798995213089059038493153)
    ·
      refine ⟨1349246409816794278869865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1798995213089059038493153 1349246409816794278869865)
      ·
        refine ⟨1011934807362595709152399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1349246409816794278869865 1011934807362595709152399)
        ·
          refine ⟨1517902211043893563728599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1011934807362595709152399 1517902211043893563728599)
          ·
            refine ⟨2276853316565840345592899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1517902211043893563728599 2276853316565840345592899)
            ·
              refine ⟨3415279974848760518389349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2276853316565840345592899 3415279974848760518389349)
              ·
                refine ⟨640364995284142597198003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3415279974848760518389349 640364995284142597198003)
                ·
                  refine ⟨960547492926213895797005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640364995284142597198003 960547492926213895797005)
                  ·
                    refine ⟨360205309847330210923877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960547492926213895797005 360205309847330210923877)
                    ·
                      rfl

theorem cell22_1052246_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_1052246 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052246 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052246 prefixEnd_1052246 := by exact prefixLift 1052246
  have htrace : WordTrace (prefixWord ++ tailWord_1052246) baseStart_1052246 baseEnd_1052246 := by
    simpa [prefixWord, tailWord_1052246, baseEnd_1052246] using wordTrace_append hprefix tailTrace_1052246
  have hstable : (prefixWord ++ tailWord_1052246).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052246).length < 2 ^ (prefixWord ++ tailWord_1052246).sum := by decide
  have hdescent : baseEnd_1052246 < baseStart_1052246 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052246) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052302 : List Nat := [4, 1, 1, 3, 1, 4, 1, 2, 2, 3]
def baseStart_1052302 : Nat := 118140960795 + 1052302 * 2 ^ 59
def prefixEnd_1052302 : Nat := 4983230072969 + 3 ^ 40 * 1052302 * 2
def baseEnd_1052302 : Nat := 360224479791764731523705

theorem tailTrace_1052302 : CollatzResearch.WordTrace tailWord_1052302 prefixEnd_1052302 360224479791764731523705 := by
  unfold tailWord_1052302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4797575879212130964819895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25587071355798031812372773 4797575879212130964819895)
  ·
    refine ⟨7196363818818196447229843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4797575879212130964819895 7196363818818196447229843)
    ·
      refine ⟨10794545728227294670844765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7196363818818196447229843 10794545728227294670844765)
      ·
        refine ⟨4047954648085235501566787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10794545728227294670844765 4047954648085235501566787)
        ·
          refine ⟨6071931972127853252350181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4047954648085235501566787 6071931972127853252350181)
          ·
            refine ⟨1138487244773972484815659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 6071931972127853252350181 1138487244773972484815659)
            ·
              refine ⟨1707730867160958727223489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138487244773972484815659 1707730867160958727223489)
              ·
                refine ⟨1280798150370719045417617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1707730867160958727223489 1280798150370719045417617)
                ·
                  refine ⟨960598612778039284063213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280798150370719045417617 960598612778039284063213)
                  ·
                    refine ⟨360224479791764731523705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960598612778039284063213 360224479791764731523705)
                    ·
                      rfl

theorem cell22_1052302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 2, 2, 3].length) (baseStart_1052302 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052302 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052302 prefixEnd_1052302 := by exact prefixLift 1052302
  have htrace : WordTrace (prefixWord ++ tailWord_1052302) baseStart_1052302 baseEnd_1052302 := by
    simpa [prefixWord, tailWord_1052302, baseEnd_1052302] using wordTrace_append hprefix tailTrace_1052302
  have hstable : (prefixWord ++ tailWord_1052302).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052302).length < 2 ^ (prefixWord ++ tailWord_1052302).sum := by decide
  have hdescent : baseEnd_1052302 < baseStart_1052302 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052319 : List Nat := [1, 1, 2, 7, 1, 1, 3, 1, 2, 3]
def baseStart_1052319 : Nat := 118140960795 + 1052319 * 2 ^ 59
def prefixEnd_1052319 : Nat := 4983230072969 + 3 ^ 40 * 1052319 * 2
def baseEnd_1052319 : Nat := 360230299239182353848653

theorem tailTrace_1052319 : CollatzResearch.WordTrace tailWord_1052319 prefixEnd_1052319 360230299239182353848653 := by
  unfold tailWord_1052319
  simp only [CollatzResearch.WordTrace]
  refine ⟨38381227074635459621928011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25587484716423639747952007 38381227074635459621928011)
  ·
    refine ⟨57571840611953189432892017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38381227074635459621928011 57571840611953189432892017)
    ·
      refine ⟨43178880458964892074669013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57571840611953189432892017 43178880458964892074669013)
      ·
        refine ⟨1012005010756989658000055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 43178880458964892074669013 1012005010756989658000055)
        ·
          refine ⟨1518007516135484487000083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1012005010756989658000055 1518007516135484487000083)
          ·
            refine ⟨2277011274203226730500125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518007516135484487000083 2277011274203226730500125)
            ·
              refine ⟨853879227826210023937547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2277011274203226730500125 853879227826210023937547)
              ·
                refine ⟨1280818841739315035906321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 853879227826210023937547 1280818841739315035906321)
                ·
                  refine ⟨960614131304486276929741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1280818841739315035906321 960614131304486276929741)
                  ·
                    refine ⟨360230299239182353848653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960614131304486276929741 360230299239182353848653)
                    ·
                      rfl

theorem cell22_1052319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 1, 1, 3, 1, 2, 3].length) (baseStart_1052319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052319 prefixEnd_1052319 := by exact prefixLift 1052319
  have htrace : WordTrace (prefixWord ++ tailWord_1052319) baseStart_1052319 baseEnd_1052319 := by
    simpa [prefixWord, tailWord_1052319, baseEnd_1052319] using wordTrace_append hprefix tailTrace_1052319
  have hstable : (prefixWord ++ tailWord_1052319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052319).length < 2 ^ (prefixWord ++ tailWord_1052319).sum := by decide
  have hdescent : baseEnd_1052319 < baseStart_1052319 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052364 : List Nat := [2, 2, 1, 5, 3, 1, 1, 1, 3, 3]
def baseStart_1052364 : Nat := 118140960795 + 1052364 * 2 ^ 59
def prefixEnd_1052364 : Nat := 4983230072969 + 3 ^ 40 * 1052364 * 2
def baseEnd_1052364 : Nat := 360245703658817236473515

theorem tailTrace_1052364 : CollatzResearch.WordTrace tailWord_1052364 prefixEnd_1052364 360245703658817236473515 := by
  unfold tailWord_1052364
  simp only [CollatzResearch.WordTrace]
  refine ⟨19191434179736216153658073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25588578906314954871544097 19191434179736216153658073)
  ·
    refine ⟨14393575634802162115243555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19191434179736216153658073 14393575634802162115243555)
    ·
      refine ⟨21590363452203243172865333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14393575634802162115243555 21590363452203243172865333)
      ·
        refine ⟨2024096573644054047456125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 21590363452203243172865333 2024096573644054047456125)
        ·
          refine ⟨759036215116520267796047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2024096573644054047456125 759036215116520267796047)
          ·
            refine ⟨1138554322674780401694071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759036215116520267796047 1138554322674780401694071)
            ·
              refine ⟨1707831484012170602541107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138554322674780401694071 1707831484012170602541107)
              ·
                refine ⟨2561747226018255903811661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707831484012170602541107 2561747226018255903811661)
                ·
                  refine ⟨960655209756845963929373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2561747226018255903811661 960655209756845963929373)
                  ·
                    refine ⟨360245703658817236473515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960655209756845963929373 360245703658817236473515)
                    ·
                      rfl

theorem cell22_1052364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 1, 3, 3].length) (baseStart_1052364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052364 prefixEnd_1052364 := by exact prefixLift 1052364
  have htrace : WordTrace (prefixWord ++ tailWord_1052364) baseStart_1052364 baseEnd_1052364 := by
    simpa [prefixWord, tailWord_1052364, baseEnd_1052364] using wordTrace_append hprefix tailTrace_1052364
  have hstable : (prefixWord ++ tailWord_1052364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052364).length < 2 ^ (prefixWord ++ tailWord_1052364).sum := by decide
  have hdescent : baseEnd_1052364 < baseStart_1052364 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052403 : List Nat := [1, 1, 1, 2, 2, 3, 2, 1, 6, 3]
def baseStart_1052403 : Nat := 118140960795 + 1052403 * 2 ^ 59
def prefixEnd_1052403 : Nat := 4983230072969 + 3 ^ 40 * 1052403 * 2
def baseEnd_1052403 : Nat := 360259054155834134748395

theorem tailTrace_1052403 : CollatzResearch.WordTrace tailWord_1052403 prefixEnd_1052403 360259054155834134748395 := by
  unfold tailWord_1052403
  simp only [CollatzResearch.WordTrace]
  refine ⟨38384290806331141967985863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25589527204220761311990575 38384290806331141967985863)
  ·
    refine ⟨57576436209496712951978795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38384290806331141967985863 57576436209496712951978795)
    ·
      refine ⟨86364654314245069427968193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57576436209496712951978795 86364654314245069427968193)
      ·
        refine ⟨64773490735683802070976145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86364654314245069427968193 64773490735683802070976145)
        ·
          refine ⟨48580118051762851553232109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64773490735683802070976145 48580118051762851553232109)
          ·
            refine ⟨18217544269411069332462041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48580118051762851553232109 18217544269411069332462041)
            ·
              refine ⟨13663158202058301999346531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18217544269411069332462041 13663158202058301999346531)
              ·
                refine ⟨20494737303087452999019797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13663158202058301999346531 20494737303087452999019797)
                ·
                  refine ⟨960690811082224359329053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20494737303087452999019797 960690811082224359329053)
                  ·
                    refine ⟨360259054155834134748395, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960690811082224359329053 360259054155834134748395)
                    ·
                      rfl

theorem cell22_1052403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 1, 6, 3].length) (baseStart_1052403 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052403 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052403 prefixEnd_1052403 := by exact prefixLift 1052403
  have htrace : WordTrace (prefixWord ++ tailWord_1052403) baseStart_1052403 baseEnd_1052403 := by
    simpa [prefixWord, tailWord_1052403, baseEnd_1052403] using wordTrace_append hprefix tailTrace_1052403
  have hstable : (prefixWord ++ tailWord_1052403).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052403).length < 2 ^ (prefixWord ++ tailWord_1052403).sum := by decide
  have hdescent : baseEnd_1052403 < baseStart_1052403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052450 : List Nat := [3, 3, 1, 1, 2, 1, 5, 6]
def baseStart_1052450 : Nat := 118140960795 + 1052450 * 2 ^ 59
def prefixEnd_1052450 : Nat := 4983230072969 + 3 ^ 40 * 1052450 * 2
def baseEnd_1052450 : Nat := 40030571468482408758139

theorem tailTrace_1052450 : CollatzResearch.WordTrace tailWord_1052450 prefixEnd_1052450 40030571468482408758139 := by
  unfold tailWord_1052450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9596501259290217248736701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25590670024773912663297869 9596501259290217248736701)
  ·
    refine ⟨3598687972233831468276263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9596501259290217248736701 3598687972233831468276263)
    ·
      refine ⟨5398031958350747202414395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3598687972233831468276263 5398031958350747202414395)
      ·
        refine ⟨8097047937526120803621593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5398031958350747202414395 8097047937526120803621593)
        ·
          refine ⟨6072785953144590602716195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8097047937526120803621593 6072785953144590602716195)
          ·
            refine ⟨9109178929716885904074293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6072785953144590602716195 9109178929716885904074293)
            ·
              refine ⟨853985524660958053506965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 9109178929716885904074293 853985524660958053506965)
              ·
                refine ⟨40030571468482408758139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 853985524660958053506965 40030571468482408758139)
                ·
                  rfl

theorem cell22_1052450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 6].length) (baseStart_1052450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052450 prefixEnd_1052450 := by exact prefixLift 1052450
  have htrace : WordTrace (prefixWord ++ tailWord_1052450) baseStart_1052450 baseEnd_1052450 := by
    simpa [prefixWord, tailWord_1052450, baseEnd_1052450] using wordTrace_append hprefix tailTrace_1052450
  have hstable : (prefixWord ++ tailWord_1052450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052450).length < 2 ^ (prefixWord ++ tailWord_1052450).sum := by decide
  have hdescent : baseEnd_1052450 < baseStart_1052450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052452 : List Nat := [2, 3, 1, 3, 2, 3, 1, 1, 2, 4]
def baseStart_1052452 : Nat := 118140960795 + 1052452 * 2 ^ 59
def prefixEnd_1052452 : Nat := 4983230072969 + 3 ^ 40 * 1052452 * 2
def baseEnd_1052452 : Nat := 360275827857214340273245

theorem tailTrace_1052452 : CollatzResearch.WordTrace tailWord_1052452 prefixEnd_1052452 360275827857214340273245 := by
  unfold tailWord_1052452
  simp only [CollatzResearch.WordTrace]
  refine ⟨19193038991576811668259805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25590718655435748891013073 19193038991576811668259805)
  ·
    refine ⟨7197389621841304375597427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19193038991576811668259805 7197389621841304375597427)
    ·
      refine ⟨10796084432761956563396141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197389621841304375597427 10796084432761956563396141)
      ·
        refine ⟨4048531662285733711273553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10796084432761956563396141 4048531662285733711273553)
        ·
          refine ⟨3036398746714300283455165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4048531662285733711273553 3036398746714300283455165)
          ·
            refine ⟨1138649530017862606295687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3036398746714300283455165 1138649530017862606295687)
            ·
              refine ⟨1707974295026793909443531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138649530017862606295687 1707974295026793909443531)
              ·
                refine ⟨2561961442540190864165297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1707974295026793909443531 2561961442540190864165297)
                ·
                  refine ⟨1921471081905143148123973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2561961442540190864165297 1921471081905143148123973)
                  ·
                    refine ⟨360275827857214340273245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921471081905143148123973 360275827857214340273245)
                    ·
                      rfl

theorem cell22_1052452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 3, 1, 1, 2, 4].length) (baseStart_1052452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052452 prefixEnd_1052452 := by exact prefixLift 1052452
  have htrace : WordTrace (prefixWord ++ tailWord_1052452) baseStart_1052452 baseEnd_1052452 := by
    simpa [prefixWord, tailWord_1052452, baseEnd_1052452] using wordTrace_append hprefix tailTrace_1052452
  have hstable : (prefixWord ++ tailWord_1052452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052452).length < 2 ^ (prefixWord ++ tailWord_1052452).sum := by decide
  have hdescent : baseEnd_1052452 < baseStart_1052452 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052516 : List Nat := [2, 3, 1, 1, 5, 2, 1, 3, 1, 3]
def baseStart_1052516 : Nat := 118140960795 + 1052516 * 2 ^ 59
def prefixEnd_1052516 : Nat := 4983230072969 + 3 ^ 40 * 1052516 * 2
def baseEnd_1052516 : Nat := 360297736365139506673049

theorem tailTrace_1052516 : CollatzResearch.WordTrace tailWord_1052516 prefixEnd_1052516 360297736365139506673049 := by
  unfold tailWord_1052516
  simp only [CollatzResearch.WordTrace]
  refine ⟨19194206127460881133424701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25592274836614508177899601 19194206127460881133424701)
  ·
    refine ⟨7197827297797830425034263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19194206127460881133424701 7197827297797830425034263)
    ·
      refine ⟨10796740946696745637551395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7197827297797830425034263 10796740946696745637551395)
      ·
        refine ⟨16195111420045118456327093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10796740946696745637551395 16195111420045118456327093)
        ·
          refine ⟨1518291695629229855280665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 16195111420045118456327093 1518291695629229855280665)
          ·
            refine ⟨1138718771721922391460499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1518291695629229855280665 1138718771721922391460499)
            ·
              refine ⟨1708078157582883587190749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1138718771721922391460499 1708078157582883587190749)
              ·
                refine ⟨640529309093581345196531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1708078157582883587190749 640529309093581345196531)
                ·
                  refine ⟨960793963640372017794797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640529309093581345196531 960793963640372017794797)
                  ·
                    refine ⟨360297736365139506673049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960793963640372017794797 360297736365139506673049)
                    ·
                      rfl

theorem cell22_1052516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 5, 2, 1, 3, 1, 3].length) (baseStart_1052516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052516 prefixEnd_1052516 := by exact prefixLift 1052516
  have htrace : WordTrace (prefixWord ++ tailWord_1052516) baseStart_1052516 baseEnd_1052516 := by
    simpa [prefixWord, tailWord_1052516, baseEnd_1052516] using wordTrace_append hprefix tailTrace_1052516
  have hstable : (prefixWord ++ tailWord_1052516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052516).length < 2 ^ (prefixWord ++ tailWord_1052516).sum := by decide
  have hdescent : baseEnd_1052516 < baseStart_1052516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052572 : List Nat := [2, 2, 3, 3, 1, 2, 1, 2, 1, 5]
def baseStart_1052572 : Nat := 118140960795 + 1052572 * 2 ^ 59
def prefixEnd_1052572 : Nat := 4983230072969 + 3 ^ 40 * 1052572 * 2
def baseEnd_1052572 : Nat := 360316906309574027272877

theorem tailTrace_1052572 : CollatzResearch.WordTrace tailWord_1052572 prefixEnd_1052572 360316906309574027272877 := by
  unfold tailWord_1052572
  simp only [CollatzResearch.WordTrace]
  refine ⟨19195227371359441915443985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25593636495145922553925313 19195227371359441915443985)
  ·
    refine ⟨14396420528519581436582989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19195227371359441915443985 14396420528519581436582989)
    ·
      refine ⟨5398657698194843038718621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14396420528519581436582989 5398657698194843038718621)
      ·
        refine ⟨2024496636823066139519483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5398657698194843038718621 2024496636823066139519483)
        ·
          refine ⟨3036744955234599209279225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024496636823066139519483 3036744955234599209279225)
          ·
            refine ⟨2277558716425949406959419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3036744955234599209279225 2277558716425949406959419)
            ·
              refine ⟨3416338074638924110439129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277558716425949406959419 3416338074638924110439129)
              ·
                refine ⟨2562253555979193082829347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3416338074638924110439129 2562253555979193082829347)
                ·
                  refine ⟨3843380333968789624244021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2562253555979193082829347 3843380333968789624244021)
                  ·
                    refine ⟨360316906309574027272877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3843380333968789624244021 360316906309574027272877)
                    ·
                      rfl

theorem cell22_1052572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 1, 2, 1, 2, 1, 5].length) (baseStart_1052572 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052572 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052572 prefixEnd_1052572 := by exact prefixLift 1052572
  have htrace : WordTrace (prefixWord ++ tailWord_1052572) baseStart_1052572 baseEnd_1052572 := by
    simpa [prefixWord, tailWord_1052572, baseEnd_1052572] using wordTrace_append hprefix tailTrace_1052572
  have hstable : (prefixWord ++ tailWord_1052572).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052572).length < 2 ^ (prefixWord ++ tailWord_1052572).sum := by decide
  have hdescent : baseEnd_1052572 < baseStart_1052572 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052647 : List Nat := [1, 1, 5, 2, 3, 1, 1, 1, 7]
def baseStart_1052647 : Nat := 118140960795 + 1052647 * 2 ^ 59
def prefixEnd_1052647 : Nat := 4983230072969 + 3 ^ 40 * 1052647 * 2
def baseEnd_1052647 : Nat := 120114193447432943882549

theorem tailTrace_1052647 : CollatzResearch.WordTrace tailWord_1052647 prefixEnd_1052647 120114193447432943882549 := by
  unfold tailWord_1052647
  simp only [CollatzResearch.WordTrace]
  refine ⟨38393190217447171639868195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25595460144964781093245463 38393190217447171639868195)
  ·
    refine ⟨57589785326170757459802293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38393190217447171639868195 57589785326170757459802293)
    ·
      refine ⟨5399042374328508511856465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57589785326170757459802293 5399042374328508511856465)
      ·
        refine ⟨4049281780746381383892349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5399042374328508511856465 4049281780746381383892349)
        ·
          refine ⟨1518480667779893018959631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4049281780746381383892349 1518480667779893018959631)
          ·
            refine ⟨2277721001669839528439447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1518480667779893018959631 2277721001669839528439447)
            ·
              refine ⟨3416581502504759292659171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2277721001669839528439447 3416581502504759292659171)
              ·
                refine ⟨5124872253757138938988757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3416581502504759292659171 5124872253757138938988757)
                ·
                  refine ⟨120114193447432943882549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5124872253757138938988757 120114193447432943882549)
                  ·
                    rfl

theorem cell22_1052647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 1, 7].length) (baseStart_1052647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052647 prefixEnd_1052647 := by exact prefixLift 1052647
  have htrace : WordTrace (prefixWord ++ tailWord_1052647) baseStart_1052647 baseEnd_1052647 := by
    simpa [prefixWord, tailWord_1052647, baseEnd_1052647] using wordTrace_append hprefix tailTrace_1052647
  have hstable : (prefixWord ++ tailWord_1052647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052647).length < 2 ^ (prefixWord ++ tailWord_1052647).sum := by decide
  have hdescent : baseEnd_1052647 < baseStart_1052647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052677 : List Nat := [1, 3, 1, 1, 2, 4, 1, 4, 1, 4]
def baseStart_1052677 : Nat := 118140960795 + 1052677 * 2 ^ 59
def prefixEnd_1052677 : Nat := 4983230072969 + 3 ^ 40 * 1052677 * 2
def baseEnd_1052677 : Nat := 360352849955388753397555

theorem tailTrace_1052677 : CollatzResearch.WordTrace tailWord_1052677 prefixEnd_1052677 360352849955388753397555 := by
  unfold tailWord_1052677
  simp only [CollatzResearch.WordTrace]
  refine ⟨38394284407338486763460285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25596189604892324508973523 38394284407338486763460285)
  ·
    refine ⟨14397856652751932536297607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38394284407338486763460285 14397856652751932536297607)
    ·
      refine ⟨21596784979127898804446411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14397856652751932536297607 21596784979127898804446411)
      ·
        refine ⟨32395177468691848206669617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21596784979127898804446411 32395177468691848206669617)
        ·
          refine ⟨24296383101518886155002213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32395177468691848206669617 24296383101518886155002213)
          ·
            refine ⟨4555571831534791154062915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24296383101518886155002213 4555571831534791154062915)
            ·
              refine ⟨6833357747302186731094373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555571831534791154062915 6833357747302186731094373)
              ·
                refine ⟨1281254577619160012080195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6833357747302186731094373 1281254577619160012080195)
                ·
                  refine ⟨1921881866428740018120293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281254577619160012080195 1921881866428740018120293)
                  ·
                    refine ⟨360352849955388753397555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1921881866428740018120293 360352849955388753397555)
                    ·
                      rfl

theorem cell22_1052677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 4, 1, 4].length) (baseStart_1052677 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052677 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052677 prefixEnd_1052677 := by exact prefixLift 1052677
  have htrace : WordTrace (prefixWord ++ tailWord_1052677) baseStart_1052677 baseEnd_1052677 := by
    simpa [prefixWord, tailWord_1052677, baseEnd_1052677] using wordTrace_append hprefix tailTrace_1052677
  have hstable : (prefixWord ++ tailWord_1052677).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052677).length < 2 ^ (prefixWord ++ tailWord_1052677).sum := by decide
  have hdescent : baseEnd_1052677 < baseStart_1052677 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052707 : List Nat := [1, 1, 1, 4, 3, 1, 1, 3, 4, 3]
def baseStart_1052707 : Nat := 118140960795 + 1052707 * 2 ^ 59
def prefixEnd_1052707 : Nat := 4983230072969 + 3 ^ 40 * 1052707 * 2
def baseEnd_1052707 : Nat := 360363119568478675147463

theorem tailTrace_1052707 : CollatzResearch.WordTrace tailWord_1052707 prefixEnd_1052707 360363119568478675147463 := by
  unfold tailWord_1052707
  simp only [CollatzResearch.WordTrace]
  refine ⟨38395378597229801887052375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25596919064819867924701583 38395378597229801887052375)
  ·
    refine ⟨57593067895844702830578563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38395378597229801887052375 57593067895844702830578563)
    ·
      refine ⟨86389601843767054245867845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57593067895844702830578563 86389601843767054245867845)
      ·
        refine ⟨16198050345706322671100221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86389601843767054245867845 16198050345706322671100221)
        ·
          refine ⟨6074268879639871001662583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16198050345706322671100221 6074268879639871001662583)
          ·
            refine ⟨9111403319459806502493875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6074268879639871001662583 9111403319459806502493875)
            ·
              refine ⟨13667104979189709753740813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9111403319459806502493875 13667104979189709753740813)
              ·
                refine ⟨5125164367196141157652805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13667104979189709753740813 5125164367196141157652805)
                ·
                  refine ⟨960968318849276467059901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5125164367196141157652805 960968318849276467059901)
                  ·
                    refine ⟨360363119568478675147463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 960968318849276467059901 360363119568478675147463)
                    ·
                      rfl

theorem cell22_1052707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 3, 4, 3].length) (baseStart_1052707 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052707 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052707 prefixEnd_1052707 := by exact prefixLift 1052707
  have htrace : WordTrace (prefixWord ++ tailWord_1052707) baseStart_1052707 baseEnd_1052707 := by
    simpa [prefixWord, tailWord_1052707, baseEnd_1052707] using wordTrace_append hprefix tailTrace_1052707
  have hstable : (prefixWord ++ tailWord_1052707).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052707).length < 2 ^ (prefixWord ++ tailWord_1052707).sum := by decide
  have hdescent : baseEnd_1052707 < baseStart_1052707 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052720 : List Nat := [2, 1, 1, 1, 2, 5, 1, 9]
def baseStart_1052720 : Nat := 118140960795 + 1052720 * 2 ^ 59
def prefixEnd_1052720 : Nat := 4983230072969 + 3 ^ 40 * 1052720 * 2
def baseEnd_1052720 : Nat := 40040841081572330508047

theorem tailTrace_1052720 : CollatzResearch.WordTrace tailWord_1052720 prefixEnd_1052720 40040841081572330508047 := by
  unfold tailWord_1052720
  simp only [CollatzResearch.WordTrace]
  refine ⟨19197926373091352553637807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25597235164121803404850409 19197926373091352553637807)
  ·
    refine ⟨28796889559637028830456711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19197926373091352553637807 28796889559637028830456711)
    ·
      refine ⟨43195334339455543245685067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28796889559637028830456711 43195334339455543245685067)
      ·
        refine ⟨64793001509183314868527601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43195334339455543245685067 64793001509183314868527601)
        ·
          refine ⟨48594751131887486151395701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64793001509183314868527601 48594751131887486151395701)
          ·
            refine ⟨4555757918614451826693347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 48594751131887486151395701 4555757918614451826693347)
            ·
              refine ⟨6833636877921677740040021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555757918614451826693347 6833636877921677740040021)
              ·
                refine ⟨40040841081572330508047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6833636877921677740040021 40040841081572330508047)
                ·
                  rfl

theorem cell22_1052720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 9].length) (baseStart_1052720 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052720 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052720 prefixEnd_1052720 := by exact prefixLift 1052720
  have htrace : WordTrace (prefixWord ++ tailWord_1052720) baseStart_1052720 baseEnd_1052720 := by
    simpa [prefixWord, tailWord_1052720, baseEnd_1052720] using wordTrace_append hprefix tailTrace_1052720
  have hstable : (prefixWord ++ tailWord_1052720).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052720).length < 2 ^ (prefixWord ++ tailWord_1052720).sum := by decide
  have hdescent : baseEnd_1052720 < baseStart_1052720 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052735 : List Nat := [1, 1, 2, 2, 3, 1, 2, 1, 2, 7]
def baseStart_1052735 : Nat := 118140960795 + 1052735 * 2 ^ 59
def prefixEnd_1052735 : Nat := 4983230072969 + 3 ^ 40 * 1052735 * 2
def baseEnd_1052735 : Nat := 360372704540695935447377

theorem tailTrace_1052735 : CollatzResearch.WordTrace tailWord_1052735 prefixEnd_1052735 360372704540695935447377 := by
  unfold tailWord_1052735
  simp only [CollatzResearch.WordTrace]
  refine ⟨38396399841128362669071659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25597599894085575112714439 38396399841128362669071659)
  ·
    refine ⟨57594599761692544003607489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38396399841128362669071659 57594599761692544003607489)
    ·
      refine ⟨43195949821269408002705617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57594599761692544003607489 43195949821269408002705617)
      ·
        refine ⟨32396962365952056002029213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43195949821269408002705617 32396962365952056002029213)
        ·
          refine ⟨12148860887232021000760955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32396962365952056002029213 12148860887232021000760955)
          ·
            refine ⟨18223291330848031501141433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12148860887232021000760955 18223291330848031501141433)
            ·
              refine ⟨13667468498136023625856075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18223291330848031501141433 13667468498136023625856075)
              ·
                refine ⟨20501202747204035438784113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13667468498136023625856075 20501202747204035438784113)
                ·
                  refine ⟨15375902060403026579088085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20501202747204035438784113 15375902060403026579088085)
                  ·
                    refine ⟨360372704540695935447377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15375902060403026579088085 360372704540695935447377)
                    ·
                      rfl

theorem cell22_1052735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 1, 2, 7].length) (baseStart_1052735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052735 prefixEnd_1052735 := by exact prefixLift 1052735
  have htrace : WordTrace (prefixWord ++ tailWord_1052735) baseStart_1052735 baseEnd_1052735 := by
    simpa [prefixWord, tailWord_1052735, baseEnd_1052735] using wordTrace_append hprefix tailTrace_1052735
  have hstable : (prefixWord ++ tailWord_1052735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052735).length < 2 ^ (prefixWord ++ tailWord_1052735).sum := by decide
  have hdescent : baseEnd_1052735 < baseStart_1052735 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052737 : List Nat := [1, 2, 5, 1, 2, 1, 2, 8]
def baseStart_1052737 : Nat := 118140960795 + 1052737 * 2 ^ 59
def prefixEnd_1052737 : Nat := 4983230072969 + 3 ^ 40 * 1052737 * 2
def baseEnd_1052737 : Nat := 40041487686840955210819

theorem tailTrace_1052737 : CollatzResearch.WordTrace tailWord_1052737 prefixEnd_1052737 40041487686840955210819 := by
  unfold tailWord_1052737
  simp only [CollatzResearch.WordTrace]
  refine ⟨38396472787121117010644465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25597648524747411340429643 38396472787121117010644465)
  ·
    refine ⟨28797354590340837757983349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38396472787121117010644465 28797354590340837757983349)
    ·
      refine ⟨2699751992844453539810939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28797354590340837757983349 2699751992844453539810939)
      ·
        refine ⟨4049627989266680309716409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2699751992844453539810939 4049627989266680309716409)
        ·
          refine ⟨3037220991950010232287307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4049627989266680309716409 3037220991950010232287307)
          ·
            refine ⟨4555831487925015348430961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037220991950010232287307 4555831487925015348430961)
            ·
              refine ⟨3416873615943761511323221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4555831487925015348430961 3416873615943761511323221)
              ·
                refine ⟨40041487686840955210819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3416873615943761511323221 40041487686840955210819)
                ·
                  rfl

theorem cell22_1052737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 8].length) (baseStart_1052737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052737 prefixEnd_1052737 := by exact prefixLift 1052737
  have htrace : WordTrace (prefixWord ++ tailWord_1052737) baseStart_1052737 baseEnd_1052737 := by
    simpa [prefixWord, tailWord_1052737, baseEnd_1052737] using wordTrace_append hprefix tailTrace_1052737
  have hstable : (prefixWord ++ tailWord_1052737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052737).length < 2 ^ (prefixWord ++ tailWord_1052737).sum := by decide
  have hdescent : baseEnd_1052737 < baseStart_1052737 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052758 : List Nat := [5, 2, 2, 1, 1, 1, 1, 4, 2, 3]
def baseStart_1052758 : Nat := 118140960795 + 1052758 * 2 ^ 59
def prefixEnd_1052758 : Nat := 4983230072969 + 3 ^ 40 * 1052758 * 2
def baseEnd_1052758 : Nat := 360380577910731542122307

theorem tailTrace_1052758 : CollatzResearch.WordTrace tailWord_1052758 prefixEnd_1052758 360380577910731542122307 := by
  unfold tailWord_1052758
  simp only [CollatzResearch.WordTrace]
  refine ⟨2399827420002814849822433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25598159146696691731439285 2399827420002814849822433)
  ·
    refine ⟨1799870565002111137366825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2399827420002814849822433 1799870565002111137366825)
    ·
      refine ⟨1349902923751583353025119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1799870565002111137366825 1349902923751583353025119)
      ·
        refine ⟨2024854385627375029537679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1349902923751583353025119 2024854385627375029537679)
        ·
          refine ⟨3037281578441062544306519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2024854385627375029537679 3037281578441062544306519)
          ·
            refine ⟨4555922367661593816459779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3037281578441062544306519 4555922367661593816459779)
            ·
              refine ⟨6833883551492390724689669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4555922367661593816459779 6833883551492390724689669)
              ·
                refine ⟨1281353165904823260879313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6833883551492390724689669 1281353165904823260879313)
                ·
                  refine ⟨961014874428617445659485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281353165904823260879313 961014874428617445659485)
                  ·
                    refine ⟨360380577910731542122307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961014874428617445659485 360380577910731542122307)
                    ·
                      rfl

theorem cell22_1052758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_1052758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052758 prefixEnd_1052758 := by exact prefixLift 1052758
  have htrace : WordTrace (prefixWord ++ tailWord_1052758) baseStart_1052758 baseEnd_1052758 := by
    simpa [prefixWord, tailWord_1052758, baseEnd_1052758] using wordTrace_append hprefix tailTrace_1052758
  have hstable : (prefixWord ++ tailWord_1052758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052758).length < 2 ^ (prefixWord ++ tailWord_1052758).sum := by decide
  have hdescent : baseEnd_1052758 < baseStart_1052758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052857 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 1, 6]
def baseStart_1052857 : Nat := 118140960795 + 1052857 * 2 ^ 59
def prefixEnd_1052857 : Nat := 4983230072969 + 3 ^ 40 * 1052857 * 2
def baseEnd_1052857 : Nat := 360414467633928283897003

theorem tailTrace_1052857 : CollatzResearch.WordTrace tailWord_1052857 prefixEnd_1052857 360414467633928283897003 := by
  unfold tailWord_1052857
  simp only [CollatzResearch.WordTrace]
  refine ⟨38400849546686377505012825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25600566364457585003341883 38400849546686377505012825)
  ·
    refine ⟨28800637160014783128759619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38400849546686377505012825 28800637160014783128759619)
    ·
      refine ⟨43200955740022174693139429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28800637160014783128759619 43200955740022174693139429)
      ·
        refine ⟨8100179201254157754963643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43200955740022174693139429 8100179201254157754963643)
        ·
          refine ⟨12150268801881236632445465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8100179201254157754963643 12150268801881236632445465)
          ·
            refine ⟨9112701601410927474334099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12150268801881236632445465 9112701601410927474334099)
            ·
              refine ⟨13669052402116391211501149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9112701601410927474334099 13669052402116391211501149)
              ·
                refine ⟨5125894650793646704312931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13669052402116391211501149 5125894650793646704312931)
                ·
                  refine ⟨7688841976190470056469397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5125894650793646704312931 7688841976190470056469397)
                  ·
                    refine ⟨360414467633928283897003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7688841976190470056469397 360414467633928283897003)
                    ·
                      rfl

theorem cell22_1052857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 1, 6].length) (baseStart_1052857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052857 prefixEnd_1052857 := by exact prefixLift 1052857
  have htrace : WordTrace (prefixWord ++ tailWord_1052857) baseStart_1052857 baseEnd_1052857 := by
    simpa [prefixWord, tailWord_1052857, baseEnd_1052857] using wordTrace_append hprefix tailTrace_1052857
  have hstable : (prefixWord ++ tailWord_1052857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052857).length < 2 ^ (prefixWord ++ tailWord_1052857).sum := by decide
  have hdescent : baseEnd_1052857 < baseStart_1052857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052874 : List Nat := [3, 1, 2, 1, 3, 1, 3, 2, 2, 4]
def baseStart_1052874 : Nat := 118140960795 + 1052874 * 2 ^ 59
def prefixEnd_1052874 : Nat := 4983230072969 + 3 ^ 40 * 1052874 * 2
def baseEnd_1052874 : Nat := 360420287081345906221951

theorem tailTrace_1052874 : CollatzResearch.WordTrace tailWord_1052874 prefixEnd_1052874 360420287081345906221951 := by
  unfold tailWord_1052874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9600367396906197352095419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25600979725083192938921117 9600367396906197352095419)
  ·
    refine ⟨14400551095359296028143129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9600367396906197352095419 14400551095359296028143129)
    ·
      refine ⟨10800413321519472021107347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14400551095359296028143129 10800413321519472021107347)
      ·
        refine ⟨16200619982279208031661021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10800413321519472021107347 16200619982279208031661021)
        ·
          refine ⟨6075232493354703011872883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16200619982279208031661021 6075232493354703011872883)
          ·
            refine ⟨9112848740032054517809325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6075232493354703011872883 9112848740032054517809325)
            ·
              refine ⟨3417318277512020444178497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9112848740032054517809325 3417318277512020444178497)
              ·
                refine ⟨2562988708134015333133873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3417318277512020444178497 2562988708134015333133873)
                ·
                  refine ⟨1922241531100511499850405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2562988708134015333133873 1922241531100511499850405)
                  ·
                    refine ⟨360420287081345906221951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922241531100511499850405 360420287081345906221951)
                    ·
                      rfl

theorem cell22_1052874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 2, 2, 4].length) (baseStart_1052874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052874 prefixEnd_1052874 := by exact prefixLift 1052874
  have htrace : WordTrace (prefixWord ++ tailWord_1052874) baseStart_1052874 baseEnd_1052874 := by
    simpa [prefixWord, tailWord_1052874, baseEnd_1052874] using wordTrace_append hprefix tailTrace_1052874
  have hstable : (prefixWord ++ tailWord_1052874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052874).length < 2 ^ (prefixWord ++ tailWord_1052874).sum := by decide
  have hdescent : baseEnd_1052874 < baseStart_1052874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052878 : List Nat := [4, 1, 1, 1, 4, 2, 3, 2, 4]
def baseStart_1052878 : Nat := 118140960795 + 1052878 * 2 ^ 59
def prefixEnd_1052878 : Nat := 4983230072969 + 3 ^ 40 * 1052878 * 2
def baseEnd_1052878 : Nat := 120140552121030409707313

theorem tailTrace_1052878 : CollatzResearch.WordTrace tailWord_1052878 prefixEnd_1052878 120140552121030409707313 := by
  unfold tailWord_1052878
  simp only [CollatzResearch.WordTrace]
  refine ⟨4800201934951287261440911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25601076986406865394351525 4800201934951287261440911)
  ·
    refine ⟨7200302902426930892161367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4800201934951287261440911 7200302902426930892161367)
    ·
      refine ⟨10800454353640396338242051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7200302902426930892161367 10800454353640396338242051)
      ·
        refine ⟨16200681530460594507363077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10800454353640396338242051 16200681530460594507363077)
        ·
          refine ⟨3037627786961361470130577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16200681530460594507363077 3037627786961361470130577)
          ·
            refine ⟨2278220840221021102597933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037627786961361470130577 2278220840221021102597933)
            ·
              refine ⟨854332815082882913474225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2278220840221021102597933 854332815082882913474225)
              ·
                refine ⟨640749611312162185105669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854332815082882913474225 640749611312162185105669)
                ·
                  refine ⟨120140552121030409707313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640749611312162185105669 120140552121030409707313)
                  ·
                    rfl

theorem cell22_1052878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 2, 3, 2, 4].length) (baseStart_1052878 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052878 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052878 prefixEnd_1052878 := by exact prefixLift 1052878
  have htrace : WordTrace (prefixWord ++ tailWord_1052878) baseStart_1052878 baseEnd_1052878 := by
    simpa [prefixWord, tailWord_1052878, baseEnd_1052878] using wordTrace_append hprefix tailTrace_1052878
  have hstable : (prefixWord ++ tailWord_1052878).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052878).length < 2 ^ (prefixWord ++ tailWord_1052878).sum := by decide
  have hdescent : baseEnd_1052878 < baseStart_1052878 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052893 : List Nat := [1, 4, 3, 2, 1, 2, 1, 3, 2, 3]
def baseStart_1052893 : Nat := 118140960795 + 1052893 * 2 ^ 59
def prefixEnd_1052893 : Nat := 4983230072969 + 3 ^ 40 * 1052893 * 2
def baseEnd_1052893 : Nat := 360426791169636189996893

theorem tailTrace_1052893 : CollatzResearch.WordTrace tailWord_1052893 prefixEnd_1052893 360426791169636189996893 := by
  unfold tailWord_1052893
  simp only [CollatzResearch.WordTrace]
  refine ⟨38402162574555955653323333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25601441716370637102215555 38402162574555955653323333)
  ·
    refine ⟨7200405482729241684998125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38402162574555955653323333 7200405482729241684998125)
    ·
      refine ⟨2700152056023465631874297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7200405482729241684998125 2700152056023465631874297)
      ·
        refine ⟨2025114042017599223905723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2700152056023465631874297 2025114042017599223905723)
        ·
          refine ⟨3037671063026398835858585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025114042017599223905723 3037671063026398835858585)
          ·
            refine ⟨2278253297269799126893939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3037671063026398835858585 2278253297269799126893939)
            ·
              refine ⟨3417379945904698690340909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2278253297269799126893939 3417379945904698690340909)
              ·
                refine ⟨1281517479714262008877841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3417379945904698690340909 1281517479714262008877841)
                ·
                  refine ⟨961138109785696506658381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1281517479714262008877841 961138109785696506658381)
                  ·
                    refine ⟨360426791169636189996893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961138109785696506658381 360426791169636189996893)
                    ·
                      rfl

theorem cell22_1052893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 3, 2, 3].length) (baseStart_1052893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052893 prefixEnd_1052893 := by exact prefixLift 1052893
  have htrace : WordTrace (prefixWord ++ tailWord_1052893) baseStart_1052893 baseEnd_1052893 := by
    simpa [prefixWord, tailWord_1052893, baseEnd_1052893] using wordTrace_append hprefix tailTrace_1052893
  have hstable : (prefixWord ++ tailWord_1052893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052893).length < 2 ^ (prefixWord ++ tailWord_1052893).sum := by decide
  have hdescent : baseEnd_1052893 < baseStart_1052893 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1052981 : List Nat := [1, 3, 3, 1, 2, 1, 3, 3, 1, 4]
def baseStart_1052981 : Nat := 118140960795 + 1052981 * 2 ^ 59
def prefixEnd_1052981 : Nat := 4983230072969 + 3 ^ 40 * 1052981 * 2
def baseEnd_1052981 : Nat := 360456915368033293796623

theorem tailTrace_1052981 : CollatzResearch.WordTrace tailWord_1052981 prefixEnd_1052981 360456915368033293796623 := by
  unfold tailWord_1052981
  simp only [CollatzResearch.WordTrace]
  refine ⟨38405372198237146682526797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25603581465491431121684531 38405372198237146682526797)
  ·
    refine ⟨14402014574338930005947549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38405372198237146682526797 14402014574338930005947549)
    ·
      refine ⟨5400755465377098752230331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14402014574338930005947549 5400755465377098752230331)
      ·
        refine ⟨8101133198065648128345497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5400755465377098752230331 8101133198065648128345497)
        ·
          refine ⟨6075849898549236096259123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8101133198065648128345497 6075849898549236096259123)
          ·
            refine ⟨9113774847823854144388685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6075849898549236096259123 9113774847823854144388685)
            ·
              refine ⟨3417665567933945304145757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9113774847823854144388685 3417665567933945304145757)
              ·
                refine ⟨1281624587975229489054659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3417665567933945304145757 1281624587975229489054659)
                ·
                  refine ⟨1922436881962844233581989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1281624587975229489054659 1922436881962844233581989)
                  ·
                    refine ⟨360456915368033293796623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1922436881962844233581989 360456915368033293796623)
                    ·
                      rfl

theorem cell22_1052981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 3, 1, 4].length) (baseStart_1052981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1052981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1052981 prefixEnd_1052981 := by exact prefixLift 1052981
  have htrace : WordTrace (prefixWord ++ tailWord_1052981) baseStart_1052981 baseEnd_1052981 := by
    simpa [prefixWord, tailWord_1052981, baseEnd_1052981] using wordTrace_append hprefix tailTrace_1052981
  have hstable : (prefixWord ++ tailWord_1052981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1052981).length < 2 ^ (prefixWord ++ tailWord_1052981).sum := by decide
  have hdescent : baseEnd_1052981 < baseStart_1052981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1052981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053009 : List Nat := [1, 2, 2, 1, 4, 2, 1, 2, 1, 6]
def baseStart_1053009 : Nat := 118140960795 + 1053009 * 2 ^ 59
def prefixEnd_1053009 : Nat := 4983230072969 + 3 ^ 40 * 1053009 * 2
def baseEnd_1053009 : Nat := 360466500340250554096537

theorem tailTrace_1053009 : CollatzResearch.WordTrace tailWord_1053009 prefixEnd_1053009 360466500340250554096537 := by
  unfold tailWord_1053009
  simp only [CollatzResearch.WordTrace]
  refine ⟨38406393442135707464546081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25604262294757138309697387 38406393442135707464546081)
  ·
    refine ⟨28804795081601780598409561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38406393442135707464546081 28804795081601780598409561)
    ·
      refine ⟨21603596311201335448807171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28804795081601780598409561 21603596311201335448807171)
      ·
        refine ⟨32405394466802003173210757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21603596311201335448807171 32405394466802003173210757)
        ·
          refine ⟨6076011462525375594977017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32405394466802003173210757 6076011462525375594977017)
          ·
            refine ⟨4557008596894031696232763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6076011462525375594977017 4557008596894031696232763)
            ·
              refine ⟨6835512895341047544349145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557008596894031696232763 6835512895341047544349145)
              ·
                refine ⟨5126634671505785658261859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6835512895341047544349145 5126634671505785658261859)
                ·
                  refine ⟨7689952007258678487392789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5126634671505785658261859 7689952007258678487392789)
                  ·
                    refine ⟨360466500340250554096537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7689952007258678487392789 360466500340250554096537)
                    ·
                      rfl

theorem cell22_1053009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 1, 2, 1, 6].length) (baseStart_1053009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053009 prefixEnd_1053009 := by exact prefixLift 1053009
  have htrace : WordTrace (prefixWord ++ tailWord_1053009) baseStart_1053009 baseEnd_1053009 := by
    simpa [prefixWord, tailWord_1053009, baseEnd_1053009] using wordTrace_append hprefix tailTrace_1053009
  have hstable : (prefixWord ++ tailWord_1053009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053009).length < 2 ^ (prefixWord ++ tailWord_1053009).sum := by decide
  have hdescent : baseEnd_1053009 < baseStart_1053009 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053026 : List Nat := [3, 3, 2, 1, 1, 2, 2, 1, 1, 6]
def baseStart_1053026 : Nat := 118140960795 + 1053026 * 2 ^ 59
def prefixEnd_1053026 : Nat := 4983230072969 + 3 ^ 40 * 1053026 * 2
def baseEnd_1053026 : Nat := 360472319787668176421485

theorem tailTrace_1053026 : CollatzResearch.WordTrace tailWord_1053026 prefixEnd_1053026 360472319787668176421485 := by
  unfold tailWord_1053026
  simp only [CollatzResearch.WordTrace]
  refine ⟨9601753370768529841978733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25604675655382746245276621 9601753370768529841978733)
  ·
    refine ⟨3600657514038198690742025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9601753370768529841978733 3600657514038198690742025)
    ·
      refine ⟨2700493135528649018056519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3600657514038198690742025 2700493135528649018056519)
      ·
        refine ⟨4050739703292973527084779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2700493135528649018056519 4050739703292973527084779)
        ·
          refine ⟨6076109554939460290627169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4050739703292973527084779 6076109554939460290627169)
          ·
            refine ⟨4557082166204595217970377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6076109554939460290627169 4557082166204595217970377)
            ·
              refine ⟨3417811624653446413477783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4557082166204595217970377 3417811624653446413477783)
              ·
                refine ⟨5126717436980169620216675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3417811624653446413477783 5126717436980169620216675)
                ·
                  refine ⟨7690076155470254430325013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5126717436980169620216675 7690076155470254430325013)
                  ·
                    refine ⟨360472319787668176421485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7690076155470254430325013 360472319787668176421485)
                    ·
                      rfl

theorem cell22_1053026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 2, 1, 1, 6].length) (baseStart_1053026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053026 prefixEnd_1053026 := by exact prefixLift 1053026
  have htrace : WordTrace (prefixWord ++ tailWord_1053026) baseStart_1053026 baseEnd_1053026 := by
    simpa [prefixWord, tailWord_1053026, baseEnd_1053026] using wordTrace_append hprefix tailTrace_1053026
  have hstable : (prefixWord ++ tailWord_1053026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053026).length < 2 ^ (prefixWord ++ tailWord_1053026).sum := by decide
  have hdescent : baseEnd_1053026 < baseStart_1053026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053090 : List Nat := [3, 3, 1, 2, 1, 1, 2, 5, 1, 3]
def baseStart_1053090 : Nat := 118140960795 + 1053090 * 2 ^ 59
def prefixEnd_1053090 : Nat := 4983230072969 + 3 ^ 40 * 1053090 * 2
def baseEnd_1053090 : Nat := 360494228295593342821289

theorem tailTrace_1053090 : CollatzResearch.WordTrace tailWord_1053090 prefixEnd_1053090 360494228295593342821289 := by
  unfold tailWord_1053090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602336938710564574561181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25606231836561505532163149 9602336938710564574561181)
  ·
    refine ⟨3600876352016461715460443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9602336938710564574561181 3600876352016461715460443)
    ·
      refine ⟨5401314528024692573190665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3600876352016461715460443 5401314528024692573190665)
      ·
        refine ⟨4050985896018519429892999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5401314528024692573190665 4050985896018519429892999)
        ·
          refine ⟨6076478844027779144839499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4050985896018519429892999 6076478844027779144839499)
          ·
            refine ⟨9114718266041668717259249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076478844027779144839499 9114718266041668717259249)
            ·
              refine ⟨6836038699531251537944437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9114718266041668717259249 6836038699531251537944437)
              ·
                refine ⟨640878628081054831682291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6836038699531251537944437 640878628081054831682291)
                ·
                  refine ⟨961317942121582247523437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640878628081054831682291 961317942121582247523437)
                  ·
                    refine ⟨360494228295593342821289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961317942121582247523437 360494228295593342821289)
                    ·
                      rfl

theorem cell22_1053090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 2, 5, 1, 3].length) (baseStart_1053090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053090 prefixEnd_1053090 := by exact prefixLift 1053090
  have htrace : WordTrace (prefixWord ++ tailWord_1053090) baseStart_1053090 baseEnd_1053090 := by
    simpa [prefixWord, tailWord_1053090, baseEnd_1053090] using wordTrace_append hprefix tailTrace_1053090
  have hstable : (prefixWord ++ tailWord_1053090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053090).length < 2 ^ (prefixWord ++ tailWord_1053090).sum := by decide
  have hdescent : baseEnd_1053090 < baseStart_1053090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053114 : List Nat := [3, 1, 1, 1, 2, 1, 1, 2, 10]
def baseStart_1053114 : Nat := 118140960795 + 1053114 * 2 ^ 59
def prefixEnd_1053114 : Nat := 4983230072969 + 3 ^ 40 * 1053114 * 2
def baseEnd_1053114 : Nat := 120167481328688426740405

theorem tailTrace_1053114 : CollatzResearch.WordTrace tailWord_1053114 prefixEnd_1053114 120167481328688426740405 := by
  unfold tailWord_1053114
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602555776688827599279599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25606815404503540264745597 9602555776688827599279599)
  ·
    refine ⟨14403833665033241398919399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9602555776688827599279599 14403833665033241398919399)
    ·
      refine ⟨21605750497549862098379099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14403833665033241398919399 21605750497549862098379099)
      ·
        refine ⟨32408625746324793147568649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21605750497549862098379099 32408625746324793147568649)
        ·
          refine ⟨24306469309743594860676487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32408625746324793147568649 24306469309743594860676487)
          ·
            refine ⟨36459703964615392291014731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24306469309743594860676487 36459703964615392291014731)
            ·
              refine ⟨54689555946923088436522097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36459703964615392291014731 54689555946923088436522097)
              ·
                refine ⟨41017166960192316327391573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54689555946923088436522097 41017166960192316327391573)
                ·
                  refine ⟨120167481328688426740405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 41017166960192316327391573 120167481328688426740405)
                  ·
                    rfl

theorem cell22_1053114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 2, 10].length) (baseStart_1053114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053114 prefixEnd_1053114 := by exact prefixLift 1053114
  have htrace : WordTrace (prefixWord ++ tailWord_1053114) baseStart_1053114 baseEnd_1053114 := by
    simpa [prefixWord, tailWord_1053114, baseEnd_1053114] using wordTrace_append hprefix tailTrace_1053114
  have hstable : (prefixWord ++ tailWord_1053114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053114).length < 2 ^ (prefixWord ++ tailWord_1053114).sum := by decide
  have hdescent : baseEnd_1053114 < baseStart_1053114 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053146 : List Nat := [3, 1, 1, 2, 3, 1, 1, 4, 1, 5]
def baseStart_1053146 : Nat := 118140960795 + 1053146 * 2 ^ 59
def prefixEnd_1053146 : Nat := 4983230072969 + 3 ^ 40 * 1053146 * 2
def baseEnd_1053146 : Nat := 360513398240027863421117

theorem tailTrace_1053146 : CollatzResearch.WordTrace tailWord_1053146 prefixEnd_1053146 360513398240027863421117 := by
  unfold tailWord_1053146
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602847560659844965570823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25607593495092919908188861 9602847560659844965570823)
  ·
    refine ⟨14404271340989767448356235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9602847560659844965570823 14404271340989767448356235)
    ·
      refine ⟨21606407011484651172534353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14404271340989767448356235 21606407011484651172534353)
      ·
        refine ⟨16204805258613488379400765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21606407011484651172534353 16204805258613488379400765)
        ·
          refine ⟨6076801971980058142275287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16204805258613488379400765 6076801971980058142275287)
          ·
            refine ⟨9115202957970087213412931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6076801971980058142275287 9115202957970087213412931)
            ·
              refine ⟨13672804436955130820119397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9115202957970087213412931 13672804436955130820119397)
              ·
                refine ⟨2563650831929087028772387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13672804436955130820119397 2563650831929087028772387)
                ·
                  refine ⟨3845476247893630543158581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2563650831929087028772387 3845476247893630543158581)
                  ·
                    refine ⟨360513398240027863421117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3845476247893630543158581 360513398240027863421117)
                    ·
                      rfl

theorem cell22_1053146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 1, 4, 1, 5].length) (baseStart_1053146 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053146 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053146 prefixEnd_1053146 := by exact prefixLift 1053146
  have htrace : WordTrace (prefixWord ++ tailWord_1053146) baseStart_1053146 baseEnd_1053146 := by
    simpa [prefixWord, tailWord_1053146, baseEnd_1053146] using wordTrace_append hprefix tailTrace_1053146
  have hstable : (prefixWord ++ tailWord_1053146).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053146).length < 2 ^ (prefixWord ++ tailWord_1053146).sum := by decide
  have hdescent : baseEnd_1053146 < baseStart_1053146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053154 : List Nat := [3, 3, 3, 2, 2, 1, 1, 2, 5]
def baseStart_1053154 : Nat := 118140960795 + 1053154 * 2 ^ 59
def prefixEnd_1053154 : Nat := 4983230072969 + 3 ^ 40 * 1053154 * 2
def baseEnd_1053154 : Nat := 120172045601172836407031

theorem tailTrace_1053154 : CollatzResearch.WordTrace tailWord_1053154 prefixEnd_1053154 120172045601172836407031 := by
  unfold tailWord_1053154
  simp only [CollatzResearch.WordTrace]
  refine ⟨9602920506652599307143629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25607788017740264819049677 9602920506652599307143629)
  ·
    refine ⟨3601095189994724740178861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9602920506652599307143629 3601095189994724740178861)
    ·
      refine ⟨1350410696248021777567073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3601095189994724740178861 1350410696248021777567073)
      ·
        refine ⟨1012808022186016333175305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1350410696248021777567073 1012808022186016333175305)
        ·
          refine ⟨759606016639512249881479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1012808022186016333175305 759606016639512249881479)
          ·
            refine ⟨1139409024959268374822219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 759606016639512249881479 1139409024959268374822219)
            ·
              refine ⟨1709113537438902562233329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139409024959268374822219 1709113537438902562233329)
              ·
                refine ⟨1281835153079176921674997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709113537438902562233329 1281835153079176921674997)
                ·
                  refine ⟨120172045601172836407031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1281835153079176921674997 120172045601172836407031)
                  ·
                    rfl

theorem cell22_1053154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 2, 5].length) (baseStart_1053154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053154 prefixEnd_1053154 := by exact prefixLift 1053154
  have htrace : WordTrace (prefixWord ++ tailWord_1053154) baseStart_1053154 baseEnd_1053154 := by
    simpa [prefixWord, tailWord_1053154, baseEnd_1053154] using wordTrace_append hprefix tailTrace_1053154
  have hstable : (prefixWord ++ tailWord_1053154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053154).length < 2 ^ (prefixWord ++ tailWord_1053154).sum := by decide
  have hdescent : baseEnd_1053154 < baseStart_1053154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053165 : List Nat := [1, 5, 1, 3, 1, 1, 2, 4, 4]
def baseStart_1053165 : Nat := 118140960795 + 1053165 * 2 ^ 59
def prefixEnd_1053165 : Nat := 4983230072969 + 3 ^ 40 * 1053165 * 2
def baseEnd_1053165 : Nat := 120173300776106049065353

theorem tailTrace_1053165 : CollatzResearch.WordTrace tailWord_1053165 prefixEnd_1053165 120173300776106049065353 := by
  unfold tailWord_1053165
  simp only [CollatzResearch.WordTrace]
  refine ⟨38412083229570546107224949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25608055486380364071483299 38412083229570546107224949)
  ·
    refine ⟨3601132802772238697552339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38412083229570546107224949 3601132802772238697552339)
    ·
      refine ⟨5401699204158358046328509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3601132802772238697552339 5401699204158358046328509)
      ·
        refine ⟨2025637201559384267373191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5401699204158358046328509 2025637201559384267373191)
        ·
          refine ⟨3038455802339076401059787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025637201559384267373191 3038455802339076401059787)
          ·
            refine ⟨4557683703508614601589681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038455802339076401059787 4557683703508614601589681)
            ·
              refine ⟨3418262777631460951192261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4557683703508614601589681 3418262777631460951192261)
              ·
                refine ⟨640924270805898928348549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3418262777631460951192261 640924270805898928348549)
                ·
                  refine ⟨120173300776106049065353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 640924270805898928348549 120173300776106049065353)
                  ·
                    rfl

theorem cell22_1053165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 4].length) (baseStart_1053165 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053165 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053165 prefixEnd_1053165 := by exact prefixLift 1053165
  have htrace : WordTrace (prefixWord ++ tailWord_1053165) baseStart_1053165 baseEnd_1053165 := by
    simpa [prefixWord, tailWord_1053165, baseEnd_1053165] using wordTrace_append hprefix tailTrace_1053165
  have hstable : (prefixWord ++ tailWord_1053165).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053165).length < 2 ^ (prefixWord ++ tailWord_1053165).sum := by decide
  have hdescent : baseEnd_1053165 < baseStart_1053165 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053197 : List Nat := [1, 7, 1, 1, 1, 1, 1, 2, 4, 3]
def baseStart_1053197 : Nat := 118140960795 + 1053197 * 2 ^ 59
def prefixEnd_1053197 : Nat := 4983230072969 + 3 ^ 40 * 1053197 * 2
def baseEnd_1053197 : Nat := 360530856582280730395961

theorem tailTrace_1053197 : CollatzResearch.WordTrace tailWord_1053197 prefixEnd_1053197 360530856582280730395961 := by
  unfold tailWord_1053197
  simp only [CollatzResearch.WordTrace]
  refine ⟨38413250365454615572389845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25608833576969743714926563 38413250365454615572389845)
  ·
    refine ⟨900310555440342552477887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 38413250365454615572389845 900310555440342552477887)
    ·
      refine ⟨1350465833160513828716831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900310555440342552477887 1350465833160513828716831)
      ·
        refine ⟨2025698749740770743075247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1350465833160513828716831 2025698749740770743075247)
        ·
          refine ⟨3038548124611156114612871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025698749740770743075247 3038548124611156114612871)
          ·
            refine ⟨4557822186916734171919307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3038548124611156114612871 4557822186916734171919307)
            ·
              refine ⟨6836733280375101257878961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4557822186916734171919307 6836733280375101257878961)
              ·
                refine ⟨5127549960281325943409221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6836733280375101257878961 5127549960281325943409221)
                ·
                  refine ⟨961415617552748614389229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5127549960281325943409221 961415617552748614389229)
                  ·
                    refine ⟨360530856582280730395961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961415617552748614389229 360530856582280730395961)
                    ·
                      rfl

theorem cell22_1053197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_1053197 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053197 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053197 prefixEnd_1053197 := by exact prefixLift 1053197
  have htrace : WordTrace (prefixWord ++ tailWord_1053197) baseStart_1053197 baseEnd_1053197 := by
    simpa [prefixWord, tailWord_1053197, baseEnd_1053197] using wordTrace_append hprefix tailTrace_1053197
  have hstable : (prefixWord ++ tailWord_1053197).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053197).length < 2 ^ (prefixWord ++ tailWord_1053197).sum := by decide
  have hdescent : baseEnd_1053197 < baseStart_1053197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053221 : List Nat := [1, 3, 1, 2, 2, 1, 4, 1, 7]
def baseStart_1053221 : Nat := 118140960795 + 1053221 * 2 ^ 59
def prefixEnd_1053221 : Nat := 4983230072969 + 3 ^ 40 * 1053221 * 2
def baseEnd_1053221 : Nat := 120179690757584222598629

theorem tailTrace_1053221 : CollatzResearch.WordTrace tailWord_1053221 prefixEnd_1053221 120179690757584222598629 := by
  unfold tailWord_1053221
  simp only [CollatzResearch.WordTrace]
  refine ⟨38414125717367667671263517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25609417144911778447509011 38414125717367667671263517)
  ·
    refine ⟨14405297144012875376723819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38414125717367667671263517 14405297144012875376723819)
    ·
      refine ⟨21607945716019313065085729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14405297144012875376723819 21607945716019313065085729)
      ·
        refine ⟨16205959287014484798814297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21607945716019313065085729 16205959287014484798814297)
        ·
          refine ⟨12154469465260863599110723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16205959287014484798814297 12154469465260863599110723)
          ·
            refine ⟨18231704197891295398666085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12154469465260863599110723 18231704197891295398666085)
            ·
              refine ⟨3418444537104617887249891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18231704197891295398666085 3418444537104617887249891)
              ·
                refine ⟨5127666805656926830874837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418444537104617887249891 5127666805656926830874837)
                ·
                  refine ⟨120179690757584222598629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5127666805656926830874837 120179690757584222598629)
                  ·
                    rfl

theorem cell22_1053221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 1, 7].length) (baseStart_1053221 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053221 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053221 prefixEnd_1053221 := by exact prefixLift 1053221
  have htrace : WordTrace (prefixWord ++ tailWord_1053221) baseStart_1053221 baseEnd_1053221 := by
    simpa [prefixWord, tailWord_1053221, baseEnd_1053221] using wordTrace_append hprefix tailTrace_1053221
  have hstable : (prefixWord ++ tailWord_1053221).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053221).length < 2 ^ (prefixWord ++ tailWord_1053221).sum := by decide
  have hdescent : baseEnd_1053221 < baseStart_1053221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053276 : List Nat := [2, 2, 4, 1, 3, 2, 2, 2, 1, 3]
def baseStart_1053276 : Nat := 118140960795 + 1053276 * 2 ^ 59
def prefixEnd_1053276 : Nat := 4983230072969 + 3 ^ 40 * 1053276 * 2
def baseEnd_1053276 : Nat := 360557899896750857670719

theorem tailTrace_1053276 : CollatzResearch.WordTrace tailWord_1053276 prefixEnd_1053276 360557899896750857670719 := by
  unfold tailWord_1053276
  simp only [CollatzResearch.WordTrace]
  refine ⟨19208065866084206032257841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25610754488112274709677121 19208065866084206032257841)
  ·
    refine ⟨14406049399563154524193381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19208065866084206032257841 14406049399563154524193381)
    ·
      refine ⟨2701134262418091473286259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14406049399563154524193381 2701134262418091473286259)
      ·
        refine ⟨4051701393627137209929389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2701134262418091473286259 4051701393627137209929389)
        ·
          refine ⟨1519388022610176453723521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4051701393627137209929389 1519388022610176453723521)
          ·
            refine ⟨1139541016957632340292641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519388022610176453723521 1139541016957632340292641)
            ·
              refine ⟨854655762718224255219481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139541016957632340292641 854655762718224255219481)
              ·
                refine ⟨640991822038668191414611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 854655762718224255219481 640991822038668191414611)
                ·
                  refine ⟨961487733058002287121917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 640991822038668191414611 961487733058002287121917)
                  ·
                    refine ⟨360557899896750857670719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961487733058002287121917 360557899896750857670719)
                    ·
                      rfl

theorem cell22_1053276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_1053276 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053276 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053276 prefixEnd_1053276 := by exact prefixLift 1053276
  have htrace : WordTrace (prefixWord ++ tailWord_1053276) baseStart_1053276 baseEnd_1053276 := by
    simpa [prefixWord, tailWord_1053276, baseEnd_1053276] using wordTrace_append hprefix tailTrace_1053276
  have hstable : (prefixWord ++ tailWord_1053276).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053276).length < 2 ^ (prefixWord ++ tailWord_1053276).sum := by decide
  have hdescent : baseEnd_1053276 < baseStart_1053276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053313 : List Nat := [1, 2, 4, 2, 1, 1, 3, 1, 1, 6]
def baseStart_1053313 : Nat := 118140960795 + 1053313 * 2 ^ 59
def prefixEnd_1053313 : Nat := 4983230072969 + 3 ^ 40 * 1053313 * 2
def baseEnd_1053313 : Nat := 360570565752895094495605

theorem tailTrace_1053313 : CollatzResearch.WordTrace tailWord_1053313 prefixEnd_1053313 360570565752895094495605 := by
  unfold tailWord_1053313
  simp only [CollatzResearch.WordTrace]
  refine ⟨38417481233034367383612593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25611654155356244922408395 38417481233034367383612593)
  ·
    refine ⟨28813110924775775537709445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38417481233034367383612593 28813110924775775537709445)
    ·
      refine ⟨5402458298395457913320521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28813110924775775537709445 5402458298395457913320521)
      ·
        refine ⟨4051843723796593434990391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5402458298395457913320521 4051843723796593434990391)
        ·
          refine ⟨6077765585694890152485587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4051843723796593434990391 6077765585694890152485587)
          ·
            refine ⟨9116648378542335228728381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6077765585694890152485587 9116648378542335228728381)
            ·
              refine ⟨3418743141953375710773143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9116648378542335228728381 3418743141953375710773143)
              ·
                refine ⟨5128114712930063566159715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418743141953375710773143 5128114712930063566159715)
                ·
                  refine ⟨7692172069395095349239573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5128114712930063566159715 7692172069395095349239573)
                  ·
                    refine ⟨360570565752895094495605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7692172069395095349239573 360570565752895094495605)
                    ·
                      rfl

theorem cell22_1053313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_1053313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053313 prefixEnd_1053313 := by exact prefixLift 1053313
  have htrace : WordTrace (prefixWord ++ tailWord_1053313) baseStart_1053313 baseEnd_1053313 := by
    simpa [prefixWord, tailWord_1053313, baseEnd_1053313] using wordTrace_append hprefix tailTrace_1053313
  have hstable : (prefixWord ++ tailWord_1053313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053313).length < 2 ^ (prefixWord ++ tailWord_1053313).sum := by decide
  have hdescent : baseEnd_1053313 < baseStart_1053313 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053332 : List Nat := [2, 4, 2, 2, 1, 2, 1, 1, 4, 3]
def baseStart_1053332 : Nat := 118140960795 + 1053332 * 2 ^ 59
def prefixEnd_1053332 : Nat := 4983230072969 + 3 ^ 40 * 1053332 * 2
def baseEnd_1053332 : Nat := 360577069841185378270547

theorem tailTrace_1053332 : CollatzResearch.WordTrace tailWord_1053332 prefixEnd_1053332 360577069841185378270547 := by
  unfold tailWord_1053332
  simp only [CollatzResearch.WordTrace]
  refine ⟨19209087109982766814277125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25612116146643689085702833 19209087109982766814277125)
  ·
    refine ⟨3601703833121768777676961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 19209087109982766814277125 3601703833121768777676961)
    ·
      refine ⟨2701277874841326583257721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3601703833121768777676961 2701277874841326583257721)
      ·
        refine ⟨2025958406130994937443291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2701277874841326583257721 2025958406130994937443291)
        ·
          refine ⟨3038937609196492406164937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2025958406130994937443291 3038937609196492406164937)
          ·
            refine ⟨2279203206897369304623703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3038937609196492406164937 2279203206897369304623703)
            ·
              refine ⟨3418804810346053956935555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2279203206897369304623703 3418804810346053956935555)
              ·
                refine ⟨5128207215519080935403333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3418804810346053956935555 5128207215519080935403333)
                ·
                  refine ⟨961538852909827675388125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5128207215519080935403333 961538852909827675388125)
                  ·
                    refine ⟨360577069841185378270547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961538852909827675388125 360577069841185378270547)
                    ·
                      rfl

theorem cell22_1053332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 1, 1, 4, 3].length) (baseStart_1053332 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053332 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053332 prefixEnd_1053332 := by exact prefixLift 1053332
  have htrace : WordTrace (prefixWord ++ tailWord_1053332) baseStart_1053332 baseEnd_1053332 := by
    simpa [prefixWord, tailWord_1053332, baseEnd_1053332] using wordTrace_append hprefix tailTrace_1053332
  have hstable : (prefixWord ++ tailWord_1053332).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053332).length < 2 ^ (prefixWord ++ tailWord_1053332).sum := by decide
  have hdescent : baseEnd_1053332 < baseStart_1053332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053373 : List Nat := [1, 4, 1, 2, 1, 3, 1, 2, 7]
def baseStart_1053373 : Nat := 118140960795 + 1053373 * 2 ^ 59
def prefixEnd_1053373 : Nat := 4983230072969 + 3 ^ 40 * 1053373 * 2
def baseEnd_1053373 : Nat := 120197034993024979331807

theorem tailTrace_1053373 : CollatzResearch.WordTrace tailWord_1053373 prefixEnd_1053373 120197034993024979331807 := by
  unfold tailWord_1053373
  simp only [CollatzResearch.WordTrace]
  refine ⟨38419669612816997630796773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25613113075211331753864515 38419669612816997630796773)
  ·
    refine ⟨7203688052403187055774395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38419669612816997630796773 7203688052403187055774395)
    ·
      refine ⟨10805532078604780583661593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7203688052403187055774395 10805532078604780583661593)
      ·
        refine ⟨8104149058953585437746195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10805532078604780583661593 8104149058953585437746195)
        ·
          refine ⟨12156223588430378156619293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104149058953585437746195 12156223588430378156619293)
          ·
            refine ⟨4558583845661391808732235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12156223588430378156619293 4558583845661391808732235)
            ·
              refine ⟨6837875768492087713098353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4558583845661391808732235 6837875768492087713098353)
              ·
                refine ⟨5128406826369065784823765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6837875768492087713098353 5128406826369065784823765)
                ·
                  refine ⟨120197034993024979331807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5128406826369065784823765 120197034993024979331807)
                  ·
                    rfl

theorem cell22_1053373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 2, 7].length) (baseStart_1053373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053373 prefixEnd_1053373 := by exact prefixLift 1053373
  have htrace : WordTrace (prefixWord ++ tailWord_1053373) baseStart_1053373 baseEnd_1053373 := by
    simpa [prefixWord, tailWord_1053373, baseEnd_1053373] using wordTrace_append hprefix tailTrace_1053373
  have hstable : (prefixWord ++ tailWord_1053373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053373).length < 2 ^ (prefixWord ++ tailWord_1053373).sum := by decide
  have hdescent : baseEnd_1053373 < baseStart_1053373 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053394 : List Nat := [3, 2, 2, 2, 3, 2, 1, 1, 3, 3]
def baseStart_1053394 : Nat := 118140960795 + 1053394 * 2 ^ 59
def prefixEnd_1053394 : Nat := 4983230072969 + 3 ^ 40 * 1053394 * 2
def baseEnd_1053394 : Nat := 360598293708237883220357

theorem tailTrace_1053394 : CollatzResearch.WordTrace tailWord_1053394 prefixEnd_1053394 360598293708237883220357 := by
  unfold tailWord_1053394
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605108886435229554327809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25613623697160612144874157 9605108886435229554327809)
  ·
    refine ⟨7203831664826422165745857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9605108886435229554327809 7203831664826422165745857)
    ·
      refine ⟨5402873748619816624309393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7203831664826422165745857 5402873748619816624309393)
      ·
        refine ⟨4052155311464862468232045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5402873748619816624309393 4052155311464862468232045)
        ·
          refine ⟨1519558241799323425587017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4052155311464862468232045 1519558241799323425587017)
          ·
            refine ⟨1139668681349492569190263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519558241799323425587017 1139668681349492569190263)
            ·
              refine ⟨1709503022024238853785395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139668681349492569190263 1709503022024238853785395)
              ·
                refine ⟨2564254533036358280678093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709503022024238853785395 2564254533036358280678093)
                ·
                  refine ⟨961595449888634355254285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2564254533036358280678093 961595449888634355254285)
                  ·
                    refine ⟨360598293708237883220357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961595449888634355254285 360598293708237883220357)
                    ·
                      rfl

theorem cell22_1053394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 2, 1, 1, 3, 3].length) (baseStart_1053394 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053394 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053394 prefixEnd_1053394 := by exact prefixLift 1053394
  have htrace : WordTrace (prefixWord ++ tailWord_1053394) baseStart_1053394 baseEnd_1053394 := by
    simpa [prefixWord, tailWord_1053394, baseEnd_1053394] using wordTrace_append hprefix tailTrace_1053394
  have hstable : (prefixWord ++ tailWord_1053394).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053394).length < 2 ^ (prefixWord ++ tailWord_1053394).sum := by decide
  have hdescent : baseEnd_1053394 < baseStart_1053394 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053407 : List Nat := [1, 1, 2, 3, 2, 5, 2, 1, 5]
def baseStart_1053407 : Nat := 118140960795 + 1053407 * 2 ^ 59
def prefixEnd_1053407 : Nat := 4983230072969 + 3 ^ 40 * 1053407 * 2
def baseEnd_1053407 : Nat := 120200914624636727548439

theorem tailTrace_1053407 : CollatzResearch.WordTrace tailWord_1053407 prefixEnd_1053407 120200914624636727548439 := by
  unfold tailWord_1053407
  simp only [CollatzResearch.WordTrace]
  refine ⟨38420909694693821437534475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25613939796462547625022983 38420909694693821437534475)
  ·
    refine ⟨57631364542040732156301713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38420909694693821437534475 57631364542040732156301713)
    ·
      refine ⟨43223523406530549117226285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57631364542040732156301713 43223523406530549117226285)
      ·
        refine ⟨16208821277448955918959857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43223523406530549117226285 16208821277448955918959857)
        ·
          refine ⟨12156615958086716939219893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16208821277448955918959857 12156615958086716939219893)
          ·
            refine ⟨1139682746070629713051865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12156615958086716939219893 1139682746070629713051865)
            ·
              refine ⟨854762059552972284788899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1139682746070629713051865 854762059552972284788899)
              ·
                refine ⟨1282143089329458427183349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854762059552972284788899 1282143089329458427183349)
                ·
                  refine ⟨120200914624636727548439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1282143089329458427183349 120200914624636727548439)
                  ·
                    rfl

theorem cell22_1053407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 2, 1, 5].length) (baseStart_1053407 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053407 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053407 prefixEnd_1053407 := by exact prefixLift 1053407
  have htrace : WordTrace (prefixWord ++ tailWord_1053407) baseStart_1053407 baseEnd_1053407 := by
    simpa [prefixWord, tailWord_1053407, baseEnd_1053407] using wordTrace_append hprefix tailTrace_1053407
  have hstable : (prefixWord ++ tailWord_1053407).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053407).length < 2 ^ (prefixWord ++ tailWord_1053407).sum := by decide
  have hdescent : baseEnd_1053407 < baseStart_1053407 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053418 : List Nat := [3, 1, 3, 1, 1, 1, 1, 3, 8]
def baseStart_1053418 : Nat := 118140960795 + 1053418 * 2 ^ 59
def prefixEnd_1053418 : Nat := 4983230072969 + 3 ^ 40 * 1053418 * 2
def baseEnd_1053418 : Nat := 120202169799569940206761

theorem tailTrace_1053418 : CollatzResearch.WordTrace tailWord_1053418 prefixEnd_1053418 120202169799569940206761 := by
  unfold tailWord_1053418
  simp only [CollatzResearch.WordTrace]
  refine ⟨9605327724413492579046227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25614207265102646877456605 9605327724413492579046227)
  ·
    refine ⟨14407991586620238868569341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9605327724413492579046227 14407991586620238868569341)
    ·
      refine ⟨5402996844982589575713503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14407991586620238868569341 5402996844982589575713503)
      ·
        refine ⟨8104495267473884363570255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5402996844982589575713503 8104495267473884363570255)
        ·
          refine ⟨12156742901210826545355383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8104495267473884363570255 12156742901210826545355383)
          ·
            refine ⟨18235114351816239818033075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12156742901210826545355383 18235114351816239818033075)
            ·
              refine ⟨27352671527724359727049613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18235114351816239818033075 27352671527724359727049613)
              ·
                refine ⟨10257251822896634897643605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27352671527724359727049613 10257251822896634897643605)
                ·
                  refine ⟨120202169799569940206761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 10257251822896634897643605 120202169799569940206761)
                  ·
                    rfl

theorem cell22_1053418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 3, 8].length) (baseStart_1053418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053418 prefixEnd_1053418 := by exact prefixLift 1053418
  have htrace : WordTrace (prefixWord ++ tailWord_1053418) baseStart_1053418 baseEnd_1053418 := by
    simpa [prefixWord, tailWord_1053418, baseEnd_1053418] using wordTrace_append hprefix tailTrace_1053418
  have hstable : (prefixWord ++ tailWord_1053418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053418).length < 2 ^ (prefixWord ++ tailWord_1053418).sum := by decide
  have hdescent : baseEnd_1053418 < baseStart_1053418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053437 : List Nat := [1, 4, 1, 1, 1, 1, 7, 1, 1, 4]
def baseStart_1053437 : Nat := 118140960795 + 1053437 * 2 ^ 59
def prefixEnd_1053437 : Nat := 4983230072969 + 3 ^ 40 * 1053437 * 2
def baseEnd_1053437 : Nat := 360613013487000104395225

theorem tailTrace_1053437 : CollatzResearch.WordTrace tailWord_1053437 prefixEnd_1053437 360613013487000104395225 := by
  unfold tailWord_1053437
  simp only [CollatzResearch.WordTrace]
  refine ⟨38422003884585136561126565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25614669256390091040751043 38422003884585136561126565)
  ·
    refine ⟨7204125728359713105211231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38422003884585136561126565 7204125728359713105211231)
    ·
      refine ⟨10806188592539569657816847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204125728359713105211231 10806188592539569657816847)
      ·
        refine ⟨16209282888809354486725271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806188592539569657816847 16209282888809354486725271)
        ·
          refine ⟨24313924333214031730087907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16209282888809354486725271 24313924333214031730087907)
          ·
            refine ⟨36470886499821047595131861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24313924333214031730087907 36470886499821047595131861)
            ·
              refine ⟨854786402339555803010903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 36470886499821047595131861 854786402339555803010903)
              ·
                refine ⟨1282179603509333704516355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 854786402339555803010903 1282179603509333704516355)
                ·
                  refine ⟨1923269405264000556774533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282179603509333704516355 1923269405264000556774533)
                  ·
                    refine ⟨360613013487000104395225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923269405264000556774533 360613013487000104395225)
                    ·
                      rfl

theorem cell22_1053437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 7, 1, 1, 4].length) (baseStart_1053437 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053437 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053437 prefixEnd_1053437 := by exact prefixLift 1053437
  have htrace : WordTrace (prefixWord ++ tailWord_1053437) baseStart_1053437 baseEnd_1053437 := by
    simpa [prefixWord, tailWord_1053437, baseEnd_1053437] using wordTrace_append hprefix tailTrace_1053437
  have hstable : (prefixWord ++ tailWord_1053437).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053437).length < 2 ^ (prefixWord ++ tailWord_1053437).sum := by decide
  have hdescent : baseEnd_1053437 < baseStart_1053437 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053495 : List Nat := [1, 1, 3, 1, 2, 1, 3, 2, 5, 3]
def baseStart_1053495 : Nat := 118140960795 + 1053495 * 2 ^ 59
def prefixEnd_1053495 : Nat := 4983230072969 + 3 ^ 40 * 1053495 * 2
def baseEnd_1053495 : Nat := 360632868072307286445047

theorem tailTrace_1053495 : CollatzResearch.WordTrace tailWord_1053495 prefixEnd_1053495 360632868072307286445047 := by
  unfold tailWord_1053495
  simp only [CollatzResearch.WordTrace]
  refine ⟨38424119318375012466737939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25616079545583341644491959 38424119318375012466737939)
  ·
    refine ⟨57636178977562518700106909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38424119318375012466737939 57636178977562518700106909)
    ·
      refine ⟨21613567116585944512540091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57636178977562518700106909 21613567116585944512540091)
      ·
        refine ⟨32420350674878916768810137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21613567116585944512540091 32420350674878916768810137)
        ·
          refine ⟨24315263006159187576607603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32420350674878916768810137 24315263006159187576607603)
          ·
            refine ⟨36472894509238781364911405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24315263006159187576607603 36472894509238781364911405)
            ·
              refine ⟨13677335440964543011841777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36472894509238781364911405 13677335440964543011841777)
              ·
                refine ⟨10258001580723407258881333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13677335440964543011841777 10258001580723407258881333)
                ·
                  refine ⟨961687648192819430520125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10258001580723407258881333 961687648192819430520125)
                  ·
                    refine ⟨360632868072307286445047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961687648192819430520125 360632868072307286445047)
                    ·
                      rfl

theorem cell22_1053495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 3, 2, 5, 3].length) (baseStart_1053495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053495 prefixEnd_1053495 := by exact prefixLift 1053495
  have htrace : WordTrace (prefixWord ++ tailWord_1053495) baseStart_1053495 baseEnd_1053495 := by
    simpa [prefixWord, tailWord_1053495, baseEnd_1053495] using wordTrace_append hprefix tailTrace_1053495
  have hstable : (prefixWord ++ tailWord_1053495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053495).length < 2 ^ (prefixWord ++ tailWord_1053495).sum := by decide
  have hdescent : baseEnd_1053495 < baseStart_1053495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053501 : List Nat := [1, 4, 1, 4, 2, 2, 1, 2, 2, 3]
def baseStart_1053501 : Nat := 118140960795 + 1053501 * 2 ^ 59
def prefixEnd_1053501 : Nat := 4983230072969 + 3 ^ 40 * 1053501 * 2
def baseEnd_1053501 : Nat := 360634921994925270795029

theorem tailTrace_1053501 : CollatzResearch.WordTrace tailWord_1053501 prefixEnd_1053501 360634921994925270795029 := by
  unfold tailWord_1053501
  simp only [CollatzResearch.WordTrace]
  refine ⟨38424338156353275491456357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25616225437568850327637571 38424338156353275491456357)
  ·
    refine ⟨7204563404316239154648067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38424338156353275491456357 7204563404316239154648067)
    ·
      refine ⟨10806845106474358731972101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7204563404316239154648067 10806845106474358731972101)
      ·
        refine ⟨2026283457463942262244769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10806845106474358731972101 2026283457463942262244769)
        ·
          refine ⟨1519712593097956696683577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2026283457463942262244769 1519712593097956696683577)
          ·
            refine ⟨1139784444823467522512683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1519712593097956696683577 1139784444823467522512683)
            ·
              refine ⟨1709676667235201283769025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139784444823467522512683 1709676667235201283769025)
              ·
                refine ⟨1282257500426400962826769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709676667235201283769025 1282257500426400962826769)
                ·
                  refine ⟨961693125319800722120077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1282257500426400962826769 961693125319800722120077)
                  ·
                    refine ⟨360634921994925270795029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961693125319800722120077 360634921994925270795029)
                    ·
                      rfl

theorem cell22_1053501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 2, 2, 3].length) (baseStart_1053501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053501 prefixEnd_1053501 := by exact prefixLift 1053501
  have htrace : WordTrace (prefixWord ++ tailWord_1053501) baseStart_1053501 baseEnd_1053501 := by
    simpa [prefixWord, tailWord_1053501, baseEnd_1053501] using wordTrace_append hprefix tailTrace_1053501
  have hstable : (prefixWord ++ tailWord_1053501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053501).length < 2 ^ (prefixWord ++ tailWord_1053501).sum := by decide
  have hdescent : baseEnd_1053501 < baseStart_1053501 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053512 : List Nat := [2, 1, 3, 1, 1, 3, 4, 1, 3, 3]
def baseStart_1053512 : Nat := 118140960795 + 1053512 * 2 ^ 59
def prefixEnd_1053512 : Nat := 4983230072969 + 3 ^ 40 * 1053512 * 2
def baseEnd_1053512 : Nat := 360638687519724908769995

theorem tailTrace_1053512 : CollatzResearch.WordTrace tailWord_1053512 prefixEnd_1053512 360638687519724908769995 := by
  unfold tailWord_1053512
  simp only [CollatzResearch.WordTrace]
  refine ⟨19212369679656712185053395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25616492906208949580071193 19212369679656712185053395)
  ·
    refine ⟨28818554519485068277580093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19212369679656712185053395 28818554519485068277580093)
    ·
      refine ⟨10806957944806900604092535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28818554519485068277580093 10806957944806900604092535)
      ·
        refine ⟨16210436917210350906138803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10806957944806900604092535 16210436917210350906138803)
        ·
          refine ⟨24315655375815526359208205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16210436917210350906138803 24315655375815526359208205)
          ·
            refine ⟨9118370765930822384703077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24315655375815526359208205 9118370765930822384703077)
            ·
              refine ⟨1709694518612029197131827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9118370765930822384703077 1709694518612029197131827)
              ·
                refine ⟨2564541777918043795697741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709694518612029197131827 2564541777918043795697741)
                ·
                  refine ⟨961703166719266423386653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2564541777918043795697741 961703166719266423386653)
                  ·
                    refine ⟨360638687519724908769995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961703166719266423386653 360638687519724908769995)
                    ·
                      rfl

theorem cell22_1053512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_1053512 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053512 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053512 prefixEnd_1053512 := by exact prefixLift 1053512
  have htrace : WordTrace (prefixWord ++ tailWord_1053512) baseStart_1053512 baseEnd_1053512 := by
    simpa [prefixWord, tailWord_1053512, baseEnd_1053512] using wordTrace_append hprefix tailTrace_1053512
  have hstable : (prefixWord ++ tailWord_1053512).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053512).length < 2 ^ (prefixWord ++ tailWord_1053512).sum := by decide
  have hdescent : baseEnd_1053512 < baseStart_1053512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053585 : List Nat := [1, 2, 2, 1, 1, 1, 3, 5, 1, 5]
def baseStart_1053585 : Nat := 118140960795 + 1053585 * 2 ^ 59
def prefixEnd_1053585 : Nat := 4983230072969 + 3 ^ 40 * 1053585 * 2
def baseEnd_1053585 : Nat := 360663676911577051694771

theorem tailTrace_1053585 : CollatzResearch.WordTrace tailWord_1053585 prefixEnd_1053585 360663676911577051694771 := by
  unfold tailWord_1053585
  simp only [CollatzResearch.WordTrace]
  refine ⟨38427401888048957837514209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25618267925365971891676139 38427401888048957837514209)
  ·
    refine ⟨28820551416036718378135657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38427401888048957837514209 28820551416036718378135657)
    ·
      refine ⟨21615413562027538783601743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28820551416036718378135657 21615413562027538783601743)
      ·
        refine ⟨32423120343041308175402615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21615413562027538783601743 32423120343041308175402615)
        ·
          refine ⟨48634680514561962263103923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32423120343041308175402615 48634680514561962263103923)
          ·
            refine ⟨72952020771842943394655885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48634680514561962263103923 72952020771842943394655885)
            ·
              refine ⟨27357007789441103772995957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72952020771842943394655885 27357007789441103772995957)
              ·
                refine ⟨2564719480260103478718371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27357007789441103772995957 2564719480260103478718371)
                ·
                  refine ⟨3847079220390155218077557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564719480260103478718371 3847079220390155218077557)
                  ·
                    refine ⟨360663676911577051694771, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3847079220390155218077557 360663676911577051694771)
                    ·
                      rfl

theorem cell22_1053585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 5].length) (baseStart_1053585 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053585 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053585 prefixEnd_1053585 := by exact prefixLift 1053585
  have htrace : WordTrace (prefixWord ++ tailWord_1053585) baseStart_1053585 baseEnd_1053585 := by
    simpa [prefixWord, tailWord_1053585, baseEnd_1053585] using wordTrace_append hprefix tailTrace_1053585
  have hstable : (prefixWord ++ tailWord_1053585).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053585).length < 2 ^ (prefixWord ++ tailWord_1053585).sum := by decide
  have hdescent : baseEnd_1053585 < baseStart_1053585 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053589 : List Nat := [1, 3, 2, 1, 1, 6, 1, 2, 1, 4]
def baseStart_1053589 : Nat := 118140960795 + 1053589 * 2 ^ 59
def prefixEnd_1053589 : Nat := 4983230072969 + 3 ^ 40 * 1053589 * 2
def baseEnd_1053589 : Nat := 360665046193322374594759

theorem tailTrace_1053589 : CollatzResearch.WordTrace tailWord_1053589 prefixEnd_1053589 360665046193322374594759 := by
  unfold tailWord_1053589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38427547780034466520659821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25618365186689644347106547 38427547780034466520659821)
  ·
    refine ⟨14410330417512924945247433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38427547780034466520659821 14410330417512924945247433)
    ·
      refine ⟨10807747813134693708935575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14410330417512924945247433 10807747813134693708935575)
      ·
        refine ⟨16211621719702040563403363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10807747813134693708935575 16211621719702040563403363)
        ·
          refine ⟨24317432579553060845105045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16211621719702040563403363 24317432579553060845105045)
          ·
            refine ⟨1139879652166549727114299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24317432579553060845105045 1139879652166549727114299)
            ·
              refine ⟨1709819478249824590671449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139879652166549727114299 1709819478249824590671449)
              ·
                refine ⟨1282364608687368443003587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1709819478249824590671449 1282364608687368443003587)
                ·
                  refine ⟨1923546913031052664505381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282364608687368443003587 1923546913031052664505381)
                  ·
                    refine ⟨360665046193322374594759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923546913031052664505381 360665046193322374594759)
                    ·
                      rfl

theorem cell22_1053589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 2, 1, 4].length) (baseStart_1053589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053589 prefixEnd_1053589 := by exact prefixLift 1053589
  have htrace : WordTrace (prefixWord ++ tailWord_1053589) baseStart_1053589 baseEnd_1053589 := by
    simpa [prefixWord, tailWord_1053589, baseEnd_1053589] using wordTrace_append hprefix tailTrace_1053589
  have hstable : (prefixWord ++ tailWord_1053589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053589).length < 2 ^ (prefixWord ++ tailWord_1053589).sum := by decide
  have hdescent : baseEnd_1053589 < baseStart_1053589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053600 : List Nat := [2, 1, 1, 4, 1, 1, 2, 3, 1, 6]
def baseStart_1053600 : Nat := 118140960795 + 1053600 * 2 ^ 59
def prefixEnd_1053600 : Nat := 4983230072969 + 3 ^ 40 * 1053600 * 2
def baseEnd_1053600 : Nat := 360668811718122012569725

theorem tailTrace_1053600 : CollatzResearch.WordTrace tailWord_1053600 prefixEnd_1053600 360668811718122012569725 := by
  unfold tailWord_1053600
  simp only [CollatzResearch.WordTrace]
  refine ⟨19213974491497307699655127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25618632655329743599540169 19213974491497307699655127)
  ·
    refine ⟨28820961737245961549482691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19213974491497307699655127 28820961737245961549482691)
    ·
      refine ⟨43231442605868942324224037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28820961737245961549482691 43231442605868942324224037)
      ·
        refine ⟨8105895488600426685792007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43231442605868942324224037 8105895488600426685792007)
        ·
          refine ⟨12158843232900640028688011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8105895488600426685792007 12158843232900640028688011)
          ·
            refine ⟨18238264849350960043032017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12158843232900640028688011 18238264849350960043032017)
            ·
              refine ⟨13678698637013220032274013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18238264849350960043032017 13678698637013220032274013)
              ·
                refine ⟨5129511988879957512102755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13678698637013220032274013 5129511988879957512102755)
                ·
                  refine ⟨7694267983319936268154133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5129511988879957512102755 7694267983319936268154133)
                  ·
                    refine ⟨360668811718122012569725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7694267983319936268154133 360668811718122012569725)
                    ·
                      rfl

theorem cell22_1053600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 3, 1, 6].length) (baseStart_1053600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053600 prefixEnd_1053600 := by exact prefixLift 1053600
  have htrace : WordTrace (prefixWord ++ tailWord_1053600) baseStart_1053600 baseEnd_1053600 := by
    simpa [prefixWord, tailWord_1053600, baseEnd_1053600] using wordTrace_append hprefix tailTrace_1053600
  have hstable : (prefixWord ++ tailWord_1053600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053600).length < 2 ^ (prefixWord ++ tailWord_1053600).sum := by decide
  have hdescent : baseEnd_1053600 < baseStart_1053600 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053602 : List Nat := [3, 3, 1, 2, 2, 1, 1, 1, 3, 5]
def baseStart_1053602 : Nat := 118140960795 + 1053602 * 2 ^ 59
def prefixEnd_1053602 : Nat := 4983230072969 + 3 ^ 40 * 1053602 * 2
def baseEnd_1053602 : Nat := 360669496358994674019719

theorem tailTrace_1053602 : CollatzResearch.WordTrace tailWord_1053602 prefixEnd_1053602 360669496358994674019719 := by
  unfold tailWord_1053602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9607005482246842435220765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25618681285991579827255373 9607005482246842435220765)
  ·
    refine ⟨3602627055842565913207787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9607005482246842435220765 3602627055842565913207787)
    ·
      refine ⟨5403940583763848869811681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3602627055842565913207787 5403940583763848869811681)
      ·
        refine ⟨4052955437822886652358761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5403940583763848869811681 4052955437822886652358761)
        ·
          refine ⟨3039716578367164989269071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4052955437822886652358761 3039716578367164989269071)
          ·
            refine ⟨4559574867550747483903607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039716578367164989269071 4559574867550747483903607)
            ·
              refine ⟨6839362301326121225855411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559574867550747483903607 6839362301326121225855411)
              ·
                refine ⟨10259043451989181838783117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839362301326121225855411 10259043451989181838783117)
                ·
                  refine ⟨3847141294495943189543669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10259043451989181838783117 3847141294495943189543669)
                  ·
                    refine ⟨360669496358994674019719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3847141294495943189543669 360669496358994674019719)
                    ·
                      rfl

theorem cell22_1053602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 1, 1, 1, 3, 5].length) (baseStart_1053602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053602 prefixEnd_1053602 := by exact prefixLift 1053602
  have htrace : WordTrace (prefixWord ++ tailWord_1053602) baseStart_1053602 baseEnd_1053602 := by
    simpa [prefixWord, tailWord_1053602, baseEnd_1053602] using wordTrace_append hprefix tailTrace_1053602
  have hstable : (prefixWord ++ tailWord_1053602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053602).length < 2 ^ (prefixWord ++ tailWord_1053602).sum := by decide
  have hdescent : baseEnd_1053602 < baseStart_1053602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053632 : List Nat := [2, 1, 1, 2, 3, 5, 1, 7]
def baseStart_1053632 : Nat := 118140960795 + 1053632 * 2 ^ 59
def prefixEnd_1053632 : Nat := 4983230072969 + 3 ^ 40 * 1053632 * 2
def baseEnd_1053632 : Nat := 40075529552453843974403

theorem tailTrace_1053632 : CollatzResearch.WordTrace tailWord_1053632 prefixEnd_1053632 40075529552453843974403 := by
  unfold tailWord_1053632
  simp only [CollatzResearch.WordTrace]
  refine ⟨19214558059439342432237575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25619410745919123242983433 19214558059439342432237575)
  ·
    refine ⟨28821837089159013648356363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19214558059439342432237575 28821837089159013648356363)
    ·
      refine ⟨43232755633738520472534545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28821837089159013648356363 43232755633738520472534545)
      ·
        refine ⟨32424566725303890354400909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43232755633738520472534545 32424566725303890354400909)
        ·
          refine ⟨12159212521988958882900341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32424566725303890354400909 12159212521988958882900341)
          ·
            refine ⟨1139926173936464895271907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12159212521988958882900341 1139926173936464895271907)
            ·
              refine ⟨1709889260904697342907861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1139926173936464895271907 1709889260904697342907861)
              ·
                refine ⟨40075529552453843974403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1709889260904697342907861 40075529552453843974403)
                ·
                  rfl

theorem cell22_1053632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 7].length) (baseStart_1053632 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053632 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053632 prefixEnd_1053632 := by exact prefixLift 1053632
  have htrace : WordTrace (prefixWord ++ tailWord_1053632) baseStart_1053632 baseEnd_1053632 := by
    simpa [prefixWord, tailWord_1053632, baseEnd_1053632] using wordTrace_append hprefix tailTrace_1053632
  have hstable : (prefixWord ++ tailWord_1053632).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053632).length < 2 ^ (prefixWord ++ tailWord_1053632).sum := by decide
  have hdescent : baseEnd_1053632 < baseStart_1053632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053636 : List Nat := [2, 3, 3, 3, 1, 1, 2, 1, 1, 5]
def baseStart_1053636 : Nat := 118140960795 + 1053636 * 2 ^ 59
def prefixEnd_1053636 : Nat := 4983230072969 + 3 ^ 40 * 1053636 * 2
def baseEnd_1053636 : Nat := 360681135253829918669615

theorem tailTrace_1053636 : CollatzResearch.WordTrace tailWord_1053636 prefixEnd_1053636 360681135253829918669615 := by
  unfold tailWord_1053636
  simp only [CollatzResearch.WordTrace]
  refine ⟨19214631005432096773810381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25619508007242795698413841 19214631005432096773810381)
  ·
    refine ⟨7205486627037036290178893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19214631005432096773810381 7205486627037036290178893)
    ·
      refine ⟨2702057485138888608817085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7205486627037036290178893 2702057485138888608817085)
      ·
        refine ⟨1013271556927083228306407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2702057485138888608817085 1013271556927083228306407)
        ·
          refine ⟨1519907335390624842459611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013271556927083228306407 1519907335390624842459611)
          ·
            refine ⟨2279861003085937263689417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1519907335390624842459611 2279861003085937263689417)
            ·
              refine ⟨1709895752314452947767063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2279861003085937263689417 1709895752314452947767063)
              ·
                refine ⟨2564843628471679421650595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1709895752314452947767063 2564843628471679421650595)
                ·
                  refine ⟨3847265442707519132475893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2564843628471679421650595 3847265442707519132475893)
                  ·
                    refine ⟨360681135253829918669615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3847265442707519132475893 360681135253829918669615)
                    ·
                      rfl

theorem cell22_1053636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 2, 1, 1, 5].length) (baseStart_1053636 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053636 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053636 prefixEnd_1053636 := by exact prefixLift 1053636
  have htrace : WordTrace (prefixWord ++ tailWord_1053636) baseStart_1053636 baseEnd_1053636 := by
    simpa [prefixWord, tailWord_1053636, baseEnd_1053636] using wordTrace_append hprefix tailTrace_1053636
  have hstable : (prefixWord ++ tailWord_1053636).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053636).length < 2 ^ (prefixWord ++ tailWord_1053636).sum := by decide
  have hdescent : baseEnd_1053636 < baseStart_1053636 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053647 : List Nat := [1, 1, 2, 1, 1, 6, 1, 1, 5, 3]
def baseStart_1053647 : Nat := 118140960795 + 1053647 * 2 ^ 59
def prefixEnd_1053647 : Nat := 4983230072969 + 3 ^ 40 * 1053647 * 2
def baseEnd_1053647 : Nat := 360684900778629556644581

theorem tailTrace_1053647 : CollatzResearch.WordTrace tailWord_1053647 prefixEnd_1053647 360684900778629556644581 := by
  unfold tailWord_1053647
  simp only [CollatzResearch.WordTrace]
  refine ⟨38429663213824342426271195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25619775475882894950847463 38429663213824342426271195)
  ·
    refine ⟨57644494820736513639406793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38429663213824342426271195 57644494820736513639406793)
    ·
      refine ⟨43233371115552385229555095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57644494820736513639406793 43233371115552385229555095)
      ·
        refine ⟨64850056673328577844332643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43233371115552385229555095 64850056673328577844332643)
        ·
          refine ⟨97275085009992866766498965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64850056673328577844332643 97275085009992866766498965)
          ·
            refine ⟨4559769609843415629679639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97275085009992866766498965 4559769609843415629679639)
            ·
              refine ⟨6839654414765123444519459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4559769609843415629679639 6839654414765123444519459)
              ·
                refine ⟨10259481622147685166779189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6839654414765123444519459 10259481622147685166779189)
                ·
                  refine ⟨961826402076345484385549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10259481622147685166779189 961826402076345484385549)
                  ·
                    refine ⟨360684900778629556644581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961826402076345484385549 360684900778629556644581)
                    ·
                      rfl

theorem cell22_1053647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 1, 1, 5, 3].length) (baseStart_1053647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053647 prefixEnd_1053647 := by exact prefixLift 1053647
  have htrace : WordTrace (prefixWord ++ tailWord_1053647) baseStart_1053647 baseEnd_1053647 := by
    simpa [prefixWord, tailWord_1053647, baseEnd_1053647] using wordTrace_append hprefix tailTrace_1053647
  have hstable : (prefixWord ++ tailWord_1053647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053647).length < 2 ^ (prefixWord ++ tailWord_1053647).sum := by decide
  have hdescent : baseEnd_1053647 < baseStart_1053647 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053681 : List Nat := [1, 2, 2, 2, 4, 1, 2, 4, 1, 3]
def baseStart_1053681 : Nat := 118140960795 + 1053681 * 2 ^ 59
def prefixEnd_1053681 : Nat := 4983230072969 + 3 ^ 40 * 1053681 * 2
def baseEnd_1053681 : Nat := 360696539673464801294477

theorem tailTrace_1053681 : CollatzResearch.WordTrace tailWord_1053681 prefixEnd_1053681 360696539673464801294477 := by
  unfold tailWord_1053681
  simp only [CollatzResearch.WordTrace]
  refine ⟨38430903295701166233008897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25620602197134110822005931 38430903295701166233008897)
  ·
    refine ⟨28823177471775874674756673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38430903295701166233008897 28823177471775874674756673)
    ·
      refine ⟨21617383103831906006067505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28823177471775874674756673 21617383103831906006067505)
      ·
        refine ⟨16213037327873929504550629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21617383103831906006067505 16213037327873929504550629)
        ·
          refine ⟨3039944498976361782103243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16213037327873929504550629 3039944498976361782103243)
          ·
            refine ⟨4559916748464542673154865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3039944498976361782103243 4559916748464542673154865)
            ·
              refine ⟨3419937561348407004866149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4559916748464542673154865 3419937561348407004866149)
              ·
                refine ⟨641238292752826313412403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3419937561348407004866149 641238292752826313412403)
                ·
                  refine ⟨961857439129239470118605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641238292752826313412403 961857439129239470118605)
                  ·
                    refine ⟨360696539673464801294477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961857439129239470118605 360696539673464801294477)
                    ·
                      rfl

theorem cell22_1053681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 1, 2, 4, 1, 3].length) (baseStart_1053681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053681 prefixEnd_1053681 := by exact prefixLift 1053681
  have htrace : WordTrace (prefixWord ++ tailWord_1053681) baseStart_1053681 baseEnd_1053681 := by
    simpa [prefixWord, tailWord_1053681, baseEnd_1053681] using wordTrace_append hprefix tailTrace_1053681
  have hstable : (prefixWord ++ tailWord_1053681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053681).length < 2 ^ (prefixWord ++ tailWord_1053681).sum := by decide
  have hdescent : baseEnd_1053681 < baseStart_1053681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053692 : List Nat := [2, 2, 2, 1, 2, 3, 2, 1, 2, 5]
def baseStart_1053692 : Nat := 118140960795 + 1053692 * 2 ^ 59
def prefixEnd_1053692 : Nat := 4983230072969 + 3 ^ 40 * 1053692 * 2
def baseEnd_1053692 : Nat := 360700305198264439269443

theorem tailTrace_1053692 : CollatzResearch.WordTrace tailWord_1053692 prefixEnd_1053692 360700305198264439269443 := by
  unfold tailWord_1053692
  simp only [CollatzResearch.WordTrace]
  refine ⟨19215652249330657555829665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25620869665774210074439553 19215652249330657555829665)
  ·
    refine ⟨14411739186997993166872249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19215652249330657555829665 14411739186997993166872249)
    ·
      refine ⟨10808804390248494875154187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14411739186997993166872249 10808804390248494875154187)
      ·
        refine ⟨16213206585372742312731281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10808804390248494875154187 16213206585372742312731281)
        ·
          refine ⟨12159904939029556734548461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16213206585372742312731281 12159904939029556734548461)
          ·
            refine ⟨4559964352136083775455673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12159904939029556734548461 4559964352136083775455673)
            ·
              refine ⟨3419973264102062831591755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4559964352136083775455673 3419973264102062831591755)
              ·
                refine ⟨5129959896153094247387633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3419973264102062831591755 5129959896153094247387633)
                ·
                  refine ⟨3847469922114820685540725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5129959896153094247387633 3847469922114820685540725)
                  ·
                    refine ⟨360700305198264439269443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3847469922114820685540725 360700305198264439269443)
                    ·
                      rfl

theorem cell22_1053692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 2, 1, 2, 5].length) (baseStart_1053692 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053692 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053692 prefixEnd_1053692 := by exact prefixLift 1053692
  have htrace : WordTrace (prefixWord ++ tailWord_1053692) baseStart_1053692 baseEnd_1053692 := by
    simpa [prefixWord, tailWord_1053692, baseEnd_1053692] using wordTrace_append hprefix tailTrace_1053692
  have hstable : (prefixWord ++ tailWord_1053692).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053692).length < 2 ^ (prefixWord ++ tailWord_1053692).sum := by decide
  have hdescent : baseEnd_1053692 < baseStart_1053692 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053758 : List Nat := [4, 2, 1, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1053758 : Nat := 118140960795 + 1053758 * 2 ^ 59
def prefixEnd_1053758 : Nat := 4983230072969 + 3 ^ 40 * 1053758 * 2
def baseEnd_1053758 : Nat := 360722898347062267119241

theorem tailTrace_1053758 : CollatzResearch.WordTrace tailWord_1053758 prefixEnd_1053758 360722898347062267119241 := by
  unfold tailWord_1053758
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804213964552776047945241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25622474477614805589041285 4804213964552776047945241)
  ·
    refine ⟨3603160473414582035958931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4804213964552776047945241 3603160473414582035958931)
    ·
      refine ⟨5404740710121873053938397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603160473414582035958931 5404740710121873053938397)
      ·
        refine ⟨2026777766295702395226899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5404740710121873053938397 2026777766295702395226899)
        ·
          refine ⟨3040166649443553592840349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026777766295702395226899 3040166649443553592840349)
          ·
            refine ⟨1140062493541332597315131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3040166649443553592840349 1140062493541332597315131)
            ·
              refine ⟨1710093740311998895972697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140062493541332597315131 1710093740311998895972697)
              ·
                refine ⟨1282570305233999171979523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1710093740311998895972697 1282570305233999171979523)
                ·
                  refine ⟨1923855457850998757969285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1282570305233999171979523 1923855457850998757969285)
                  ·
                    refine ⟨360722898347062267119241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1923855457850998757969285 360722898347062267119241)
                    ·
                      rfl

theorem cell22_1053758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1053758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053758 prefixEnd_1053758 := by exact prefixLift 1053758
  have htrace : WordTrace (prefixWord ++ tailWord_1053758) baseStart_1053758 baseEnd_1053758 := by
    simpa [prefixWord, tailWord_1053758, baseEnd_1053758] using wordTrace_append hprefix tailTrace_1053758
  have hstable : (prefixWord ++ tailWord_1053758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053758).length < 2 ^ (prefixWord ++ tailWord_1053758).sum := by decide
  have hdescent : baseEnd_1053758 < baseStart_1053758 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053767 : List Nat := [1, 1, 4, 1, 3, 2, 2, 8]
def baseStart_1053767 : Nat := 118140960795 + 1053767 * 2 ^ 59
def prefixEnd_1053767 : Nat := 4983230072969 + 3 ^ 40 * 1053767 * 2
def baseEnd_1053767 : Nat := 40080664358998804849357

theorem tailTrace_1053767 : CollatzResearch.WordTrace tailWord_1053767 prefixEnd_1053767 40080664358998804849357 := by
  unfold tailWord_1053767
  simp only [CollatzResearch.WordTrace]
  refine ⟨38434039973389602920639555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25622693315593068613759703 38434039973389602920639555)
  ·
    refine ⟨57651059960084404380959333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38434039973389602920639555 57651059960084404380959333)
    ·
      refine ⟨10809573742515825821429875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57651059960084404380959333 10809573742515825821429875)
      ·
        refine ⟨16214360613773738732144813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10809573742515825821429875 16214360613773738732144813)
        ·
          refine ⟨6080385230165152024554305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16214360613773738732144813 6080385230165152024554305)
          ·
            refine ⟨4560288922623864018415729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6080385230165152024554305 4560288922623864018415729)
            ·
              refine ⟨3420216691967898013811797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4560288922623864018415729 3420216691967898013811797)
              ·
                refine ⟨40080664358998804849357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3420216691967898013811797 40080664358998804849357)
                ·
                  rfl

theorem cell22_1053767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 8].length) (baseStart_1053767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053767 prefixEnd_1053767 := by exact prefixLift 1053767
  have htrace : WordTrace (prefixWord ++ tailWord_1053767) baseStart_1053767 baseEnd_1053767 := by
    simpa [prefixWord, tailWord_1053767, baseEnd_1053767] using wordTrace_append hprefix tailTrace_1053767
  have hstable : (prefixWord ++ tailWord_1053767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053767).length < 2 ^ (prefixWord ++ tailWord_1053767).sum := by decide
  have hdescent : baseEnd_1053767 < baseStart_1053767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053790 : List Nat := [4, 4, 1, 1, 1, 2, 1, 4, 4]
def baseStart_1053790 : Nat := 118140960795 + 1053790 * 2 ^ 59
def prefixEnd_1053790 : Nat := 4983230072969 + 3 ^ 40 * 1053790 * 2
def baseEnd_1053790 : Nat := 120244617533674950106381

theorem tailTrace_1053790 : CollatzResearch.WordTrace tailWord_1053790 prefixEnd_1053790 120244617533674950106381 := by
  unfold tailWord_1053790
  simp only [CollatzResearch.WordTrace]
  refine ⟨4804359856538284731090853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25623252568204185232484549 4804359856538284731090853)
  ·
    refine ⟨900817473100928387079535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4804359856538284731090853 900817473100928387079535)
    ·
      refine ⟨1351226209651392580619303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 900817473100928387079535 1351226209651392580619303)
      ·
        refine ⟨2026839314477088870928955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1351226209651392580619303 2026839314477088870928955)
        ·
          refine ⟨3040258971715633306393433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026839314477088870928955 3040258971715633306393433)
          ·
            refine ⟨2280194228786724979795075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3040258971715633306393433 2280194228786724979795075)
            ·
              refine ⟨3420291343180087469692613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280194228786724979795075 3420291343180087469692613)
              ·
                refine ⟨641304626846266400567365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3420291343180087469692613 641304626846266400567365)
                ·
                  refine ⟨120244617533674950106381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641304626846266400567365 120244617533674950106381)
                  ·
                    rfl

theorem cell22_1053790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 2, 1, 4, 4].length) (baseStart_1053790 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053790 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053790 prefixEnd_1053790 := by exact prefixLift 1053790
  have htrace : WordTrace (prefixWord ++ tailWord_1053790) baseStart_1053790 baseEnd_1053790 := by
    simpa [prefixWord, tailWord_1053790, baseEnd_1053790] using wordTrace_append hprefix tailTrace_1053790
  have hstable : (prefixWord ++ tailWord_1053790).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053790).length < 2 ^ (prefixWord ++ tailWord_1053790).sum := by decide
  have hdescent : baseEnd_1053790 < baseStart_1053790 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053797 : List Nat := [1, 3, 1, 3, 2, 1, 1, 1, 1, 8]
def baseStart_1053797 : Nat := 118140960795 + 1053797 * 2 ^ 59
def prefixEnd_1053797 : Nat := 4983230072969 + 3 ^ 40 * 1053797 * 2
def baseEnd_1053797 : Nat := 360736248844079165394121

theorem tailTrace_1053797 : CollatzResearch.WordTrace tailWord_1053797 prefixEnd_1053797 360736248844079165394121 := by
  unfold tailWord_1053797
  simp only [CollatzResearch.WordTrace]
  refine ⟨38435134163280918044231645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25623422775520612029487763 38435134163280918044231645)
  ·
    refine ⟨14413175311230344266586867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38435134163280918044231645 14413175311230344266586867)
    ·
      refine ⟨21619762966845516399880301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14413175311230344266586867 21619762966845516399880301)
      ·
        refine ⟨8107411112567068649955113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21619762966845516399880301 8107411112567068649955113)
        ·
          refine ⟨6080558334425301487466335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8107411112567068649955113 6080558334425301487466335)
          ·
            refine ⟨9120837501637952231199503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080558334425301487466335 9120837501637952231199503)
            ·
              refine ⟨13681256252456928346799255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120837501637952231199503 13681256252456928346799255)
              ·
                refine ⟨20521884378685392520198883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13681256252456928346799255 20521884378685392520198883)
                ·
                  refine ⟨30782826568028088780298325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20521884378685392520198883 30782826568028088780298325)
                  ·
                    refine ⟨360736248844079165394121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 30782826568028088780298325 360736248844079165394121)
                    ·
                      rfl

theorem cell22_1053797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 1, 1, 8].length) (baseStart_1053797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053797 prefixEnd_1053797 := by exact prefixLift 1053797
  have htrace : WordTrace (prefixWord ++ tailWord_1053797) baseStart_1053797 baseEnd_1053797 := by
    simpa [prefixWord, tailWord_1053797, baseEnd_1053797] using wordTrace_append hprefix tailTrace_1053797
  have hstable : (prefixWord ++ tailWord_1053797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053797).length < 2 ^ (prefixWord ++ tailWord_1053797).sum := by decide
  have hdescent : baseEnd_1053797 < baseStart_1053797 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053814 : List Nat := [5, 1, 1, 2, 1, 1, 1, 2, 2, 6]
def baseStart_1053814 : Nat := 118140960795 + 1053814 * 2 ^ 59
def prefixEnd_1053814 : Nat := 4983230072969 + 3 ^ 40 * 1053814 * 2
def baseEnd_1053814 : Nat := 360742068291496787719069

theorem tailTrace_1053814 : CollatzResearch.WordTrace tailWord_1053814 prefixEnd_1053814 360742068291496787719069 := by
  unfold tailWord_1053814
  simp only [CollatzResearch.WordTrace]
  refine ⟨2402234637763708121725031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25623836136146219965066997 2402234637763708121725031)
  ·
    refine ⟨3603351956645562182587547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2402234637763708121725031 3603351956645562182587547)
    ·
      refine ⟨5405027934968343273881321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3603351956645562182587547 5405027934968343273881321)
      ·
        refine ⟨4053770951226257455410991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5405027934968343273881321 4053770951226257455410991)
        ·
          refine ⟨6080656426839386183116487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4053770951226257455410991 6080656426839386183116487)
          ·
            refine ⟨9120984640259079274674731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6080656426839386183116487 9120984640259079274674731)
            ·
              refine ⟨13681476960388618912012097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9120984640259079274674731 13681476960388618912012097)
              ·
                refine ⟨10261107720291464184009073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13681476960388618912012097 10261107720291464184009073)
                ·
                  refine ⟨7695830790218598138006805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10261107720291464184009073 7695830790218598138006805)
                  ·
                    refine ⟨360742068291496787719069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7695830790218598138006805 360742068291496787719069)
                    ·
                      rfl

theorem cell22_1053814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_1053814 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053814 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053814 prefixEnd_1053814 := by exact prefixLift 1053814
  have htrace : WordTrace (prefixWord ++ tailWord_1053814) baseStart_1053814 baseEnd_1053814 := by
    simpa [prefixWord, tailWord_1053814, baseEnd_1053814] using wordTrace_append hprefix tailTrace_1053814
  have hstable : (prefixWord ++ tailWord_1053814).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053814).length < 2 ^ (prefixWord ++ tailWord_1053814).sum := by decide
  have hdescent : baseEnd_1053814 < baseStart_1053814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053827 : List Nat := [1, 1, 1, 3, 3, 2, 1, 2, 1, 7]
def baseStart_1053827 : Nat := 118140960795 + 1053827 * 2 ^ 59
def prefixEnd_1053827 : Nat := 4983230072969 + 3 ^ 40 * 1053827 * 2
def baseEnd_1053827 : Nat := 360746518457169087144029

theorem tailTrace_1053827 : CollatzResearch.WordTrace tailWord_1053827 prefixEnd_1053827 360746518457169087144029 := by
  unfold tailWord_1053827
  simp only [CollatzResearch.WordTrace]
  refine ⟨38436228353172233167823735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25624152235448155445215823 38436228353172233167823735)
  ·
    refine ⟨57654342529758349751735603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38436228353172233167823735 57654342529758349751735603)
    ·
      refine ⟨86481513794637524627603405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57654342529758349751735603 86481513794637524627603405)
      ·
        refine ⟨32430567672989071735351277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86481513794637524627603405 32430567672989071735351277)
        ·
          refine ⟨12161462877370901900756729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32430567672989071735351277 12161462877370901900756729)
          ·
            refine ⟨9121097158028176425567547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12161462877370901900756729 9121097158028176425567547)
            ·
              refine ⟨13681645737042264638351321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9121097158028176425567547 13681645737042264638351321)
              ·
                refine ⟨10261234302781698478763491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13681645737042264638351321 10261234302781698478763491)
                ·
                  refine ⟨15391851454172547718145237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10261234302781698478763491 15391851454172547718145237)
                  ·
                    refine ⟨360746518457169087144029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15391851454172547718145237 360746518457169087144029)
                    ·
                      rfl

theorem cell22_1053827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 2, 1, 7].length) (baseStart_1053827 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053827 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053827 prefixEnd_1053827 := by exact prefixLift 1053827
  have htrace : WordTrace (prefixWord ++ tailWord_1053827) baseStart_1053827 baseEnd_1053827 := by
    simpa [prefixWord, tailWord_1053827, baseEnd_1053827] using wordTrace_append hprefix tailTrace_1053827
  have hstable : (prefixWord ++ tailWord_1053827).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053827).length < 2 ^ (prefixWord ++ tailWord_1053827).sum := by decide
  have hdescent : baseEnd_1053827 < baseStart_1053827 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053833 : List Nat := [1, 2, 1, 1, 4, 4, 2, 3, 1, 3]
def baseStart_1053833 : Nat := 118140960795 + 1053833 * 2 ^ 59
def prefixEnd_1053833 : Nat := 4983230072969 + 3 ^ 40 * 1053833 * 2
def baseEnd_1053833 : Nat := 360748572379787071494011

theorem tailTrace_1053833 : CollatzResearch.WordTrace tailWord_1053833 prefixEnd_1053833 360748572379787071494011 := by
  unfold tailWord_1053833
  simp only [CollatzResearch.WordTrace]
  refine ⟨38436447191150496192542153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25624298127433664128361435 38436447191150496192542153)
  ·
    refine ⟨28827335393362872144406615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38436447191150496192542153 28827335393362872144406615)
    ·
      refine ⟨43241003090044308216609923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28827335393362872144406615 43241003090044308216609923)
      ·
        refine ⟨64861504635066462324914885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43241003090044308216609923 64861504635066462324914885)
        ·
          refine ⟨12161532119074961685921541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64861504635066462324914885 12161532119074961685921541)
          ·
            refine ⟨2280287272326555316110289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12161532119074961685921541 2280287272326555316110289)
            ·
              refine ⟨1710215454244916487082717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280287272326555316110289 1710215454244916487082717)
              ·
                refine ⟨641330795341843682656019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1710215454244916487082717 641330795341843682656019)
                ·
                  refine ⟨961996193012765523984029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641330795341843682656019 961996193012765523984029)
                  ·
                    refine ⟨360748572379787071494011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 961996193012765523984029 360748572379787071494011)
                    ·
                      rfl

theorem cell22_1053833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 2, 3, 1, 3].length) (baseStart_1053833 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053833 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053833 prefixEnd_1053833 := by exact prefixLift 1053833
  have htrace : WordTrace (prefixWord ++ tailWord_1053833) baseStart_1053833 baseEnd_1053833 := by
    simpa [prefixWord, tailWord_1053833, baseEnd_1053833] using wordTrace_append hprefix tailTrace_1053833
  have hstable : (prefixWord ++ tailWord_1053833).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053833).length < 2 ^ (prefixWord ++ tailWord_1053833).sum := by decide
  have hdescent : baseEnd_1053833 < baseStart_1053833 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053863 : List Nat := [1, 1, 6, 2, 1, 2, 3, 1, 5]
def baseStart_1053863 : Nat := 118140960795 + 1053863 * 2 ^ 59
def prefixEnd_1053863 : Nat := 4983230072969 + 3 ^ 40 * 1053863 * 2
def baseEnd_1053863 : Nat := 120252947330958997747973

theorem tailTrace_1053863 : CollatzResearch.WordTrace tailWord_1053863 prefixEnd_1053863 120252947330958997747973 := by
  unfold tailWord_1053863
  simp only [CollatzResearch.WordTrace]
  refine ⟨38437541381041811316134243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25625027587361207544089495 38437541381041811316134243)
  ·
    refine ⟨57656312071562716974201365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38437541381041811316134243 57656312071562716974201365)
    ·
      refine ⟨2702639628354502358165689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 57656312071562716974201365 2702639628354502358165689)
      ·
        refine ⟨2026979721265876768624267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2702639628354502358165689 2026979721265876768624267)
        ·
          refine ⟨3040469581898815152936401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2026979721265876768624267 3040469581898815152936401)
          ·
            refine ⟨2280352186424111364702301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3040469581898815152936401 2280352186424111364702301)
            ·
              refine ⟨855132069909041761763363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2280352186424111364702301 855132069909041761763363)
              ·
                refine ⟨1282698104863562642645045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855132069909041761763363 1282698104863562642645045)
                ·
                  refine ⟨120252947330958997747973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1282698104863562642645045 120252947330958997747973)
                  ·
                    rfl

theorem cell22_1053863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 3, 1, 5].length) (baseStart_1053863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053863 prefixEnd_1053863 := by exact prefixLift 1053863
  have htrace : WordTrace (prefixWord ++ tailWord_1053863) baseStart_1053863 baseEnd_1053863 := by
    simpa [prefixWord, tailWord_1053863, baseEnd_1053863] using wordTrace_append hprefix tailTrace_1053863
  have hstable : (prefixWord ++ tailWord_1053863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053863).length < 2 ^ (prefixWord ++ tailWord_1053863).sum := by decide
  have hdescent : baseEnd_1053863 < baseStart_1053863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053874 : List Nat := [3, 2, 1, 1, 1, 4, 2, 2, 6]
def baseStart_1053874 : Nat := 118140960795 + 1053874 * 2 ^ 59
def prefixEnd_1053874 : Nat := 4983230072969 + 3 ^ 40 * 1053874 * 2
def baseEnd_1053874 : Nat := 120254202505892210406295

theorem tailTrace_1053874 : CollatzResearch.WordTrace tailWord_1053874 prefixEnd_1053874 120254202505892210406295 := by
  unfold tailWord_1053874
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609485646000490048696169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25625295056001306796523117 9609485646000490048696169)
  ·
    refine ⟨7207114234500367536522127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9609485646000490048696169 7207114234500367536522127)
    ·
      refine ⟨10810671351750551304783191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207114234500367536522127 10810671351750551304783191)
      ·
        refine ⟨16216007027625826957174787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10810671351750551304783191 16216007027625826957174787)
        ·
          refine ⟨24324010541438740435762181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16216007027625826957174787 24324010541438740435762181)
          ·
            refine ⟨4560751976519763831705409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24324010541438740435762181 4560751976519763831705409)
            ·
              refine ⟨3420563982389822873779057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4560751976519763831705409 3420563982389822873779057)
              ·
                refine ⟨2565422986792367155334293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3420563982389822873779057 2565422986792367155334293)
                ·
                  refine ⟨120254202505892210406295, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2565422986792367155334293 120254202505892210406295)
                  ·
                    rfl

theorem cell22_1053874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 2, 6].length) (baseStart_1053874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053874 prefixEnd_1053874 := by exact prefixLift 1053874
  have htrace : WordTrace (prefixWord ++ tailWord_1053874) baseStart_1053874 baseEnd_1053874 := by
    simpa [prefixWord, tailWord_1053874, baseEnd_1053874] using wordTrace_append hprefix tailTrace_1053874
  have hstable : (prefixWord ++ tailWord_1053874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053874).length < 2 ^ (prefixWord ++ tailWord_1053874).sum := by decide
  have hdescent : baseEnd_1053874 < baseStart_1053874 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053906 : List Nat := [3, 2, 2, 2, 1, 1, 1, 3, 4, 3]
def baseStart_1053906 : Nat := 118140960795 + 1053906 * 2 ^ 59
def prefixEnd_1053906 : Nat := 4983230072969 + 3 ^ 40 * 1053906 * 2
def baseEnd_1053906 : Nat := 360773561771639214418787

theorem tailTrace_1053906 : CollatzResearch.WordTrace tailWord_1053906 prefixEnd_1053906 360773561771639214418787 := by
  unfold tailWord_1053906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9609777429971507414987393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25626073146590686439966381 9609777429971507414987393)
  ·
    refine ⟨7207333072478630561240545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9609777429971507414987393 7207333072478630561240545)
    ·
      refine ⟨5405499804358972920930409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7207333072478630561240545 5405499804358972920930409)
      ·
        refine ⟨4054124853269229690697807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5405499804358972920930409 4054124853269229690697807)
        ·
          refine ⟨6081187279903844536046711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4054124853269229690697807 6081187279903844536046711)
          ·
            refine ⟨9121780919855766804070067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6081187279903844536046711 9121780919855766804070067)
            ·
              refine ⟨13682671379783650206105101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9121780919855766804070067 13682671379783650206105101)
              ·
                refine ⟨5131001767418868827289413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13682671379783650206105101 5131001767418868827289413)
                ·
                  refine ⟨962062831391037905116765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5131001767418868827289413 962062831391037905116765)
                  ·
                    refine ⟨360773561771639214418787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962062831391037905116765 360773561771639214418787)
                    ·
                      rfl

theorem cell22_1053906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 3, 4, 3].length) (baseStart_1053906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053906 prefixEnd_1053906 := by exact prefixLift 1053906
  have htrace : WordTrace (prefixWord ++ tailWord_1053906) baseStart_1053906 baseEnd_1053906 := by
    simpa [prefixWord, tailWord_1053906, baseEnd_1053906] using wordTrace_append hprefix tailTrace_1053906
  have hstable : (prefixWord ++ tailWord_1053906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053906).length < 2 ^ (prefixWord ++ tailWord_1053906).sum := by decide
  have hdescent : baseEnd_1053906 < baseStart_1053906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053934 : List Nat := [4, 1, 2, 1, 1, 1, 2, 1, 2, 7]
def baseStart_1053934 : Nat := 118140960795 + 1053934 * 2 ^ 59
def prefixEnd_1053934 : Nat := 4983230072969 + 3 ^ 40 * 1053934 * 2
def baseEnd_1053934 : Nat := 360783146743856474718701

theorem tailTrace_1053934 : CollatzResearch.WordTrace tailWord_1053934 prefixEnd_1053934 360783146743856474718701 := by
  unfold tailWord_1053934
  simp only [CollatzResearch.WordTrace]
  refine ⟨4805016370473073805246107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25626753975856393627979237 4805016370473073805246107)
  ·
    refine ⟨7207524555709610707869161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4805016370473073805246107 7207524555709610707869161)
    ·
      refine ⟨5405643416782208030901871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7207524555709610707869161 5405643416782208030901871)
      ·
        refine ⟨8108465125173312046352807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5405643416782208030901871 8108465125173312046352807)
        ·
          refine ⟨12162697687759968069529211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8108465125173312046352807 12162697687759968069529211)
          ·
            refine ⟨18244046531639952104293817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12162697687759968069529211 18244046531639952104293817)
            ·
              refine ⟨13683034898729964078220363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18244046531639952104293817 13683034898729964078220363)
              ·
                refine ⟨20524552348094946117330545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13683034898729964078220363 20524552348094946117330545)
                ·
                  refine ⟨15393414261071209587997909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20524552348094946117330545 15393414261071209587997909)
                  ·
                    refine ⟨360783146743856474718701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15393414261071209587997909 360783146743856474718701)
                    ·
                      rfl

theorem cell22_1053934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 2, 7].length) (baseStart_1053934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053934 prefixEnd_1053934 := by exact prefixLift 1053934
  have htrace : WordTrace (prefixWord ++ tailWord_1053934) baseStart_1053934 baseEnd_1053934 := by
    simpa [prefixWord, tailWord_1053934, baseEnd_1053934] using wordTrace_append hprefix tailTrace_1053934
  have hstable : (prefixWord ++ tailWord_1053934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053934).length < 2 ^ (prefixWord ++ tailWord_1053934).sum := by decide
  have hdescent : baseEnd_1053934 < baseStart_1053934 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053938 : List Nat := [3, 2, 1, 3, 3, 1, 2, 1, 2, 4]
def baseStart_1053938 : Nat := 118140960795 + 1053938 * 2 ^ 59
def prefixEnd_1053938 : Nat := 4983230072969 + 3 ^ 40 * 1053938 * 2
def baseEnd_1053938 : Nat := 360784516025601797618689

theorem tailTrace_1053938 : CollatzResearch.WordTrace tailWord_1053938 prefixEnd_1053938 360784516025601797618689 := by
  unfold tailWord_1053938
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610069213942524781278617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25626851237180066083409645 9610069213942524781278617)
  ·
    refine ⟨7207551910456893585958963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9610069213942524781278617 7207551910456893585958963)
    ·
      refine ⟨10811327865685340378938445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7207551910456893585958963 10811327865685340378938445)
      ·
        refine ⟨4054247949632002642101917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10811327865685340378938445 4054247949632002642101917)
        ·
          refine ⟨1520342981112000990788219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4054247949632002642101917 1520342981112000990788219)
          ·
            refine ⟨2280514471668001486182329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520342981112000990788219 2280514471668001486182329)
            ·
              refine ⟨1710385853751001114636747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2280514471668001486182329 1710385853751001114636747)
              ·
                refine ⟨2565578780626501671955121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710385853751001114636747 2565578780626501671955121)
                ·
                  refine ⟨1924184085469876253966341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2565578780626501671955121 1924184085469876253966341)
                  ·
                    refine ⟨360784516025601797618689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1924184085469876253966341 360784516025601797618689)
                    ·
                      rfl

theorem cell22_1053938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 3, 1, 2, 1, 2, 4].length) (baseStart_1053938 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053938 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053938 prefixEnd_1053938 := by exact prefixLift 1053938
  have htrace : WordTrace (prefixWord ++ tailWord_1053938) baseStart_1053938 baseEnd_1053938 := by
    simpa [prefixWord, tailWord_1053938, baseEnd_1053938] using wordTrace_append hprefix tailTrace_1053938
  have hstable : (prefixWord ++ tailWord_1053938).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053938).length < 2 ^ (prefixWord ++ tailWord_1053938).sum := by decide
  have hdescent : baseEnd_1053938 < baseStart_1053938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1053970 : List Nat := [3, 2, 4, 2, 1, 2, 1, 7]
def baseStart_1053970 : Nat := 118140960795 + 1053970 * 2 ^ 59
def prefixEnd_1053970 : Nat := 4983230072969 + 3 ^ 40 * 1053970 * 2
def baseEnd_1053970 : Nat := 40088385586618264535399

theorem tailTrace_1053970 : CollatzResearch.WordTrace tailWord_1053970 prefixEnd_1053970 40088385586618264535399 := by
  unfold tailWord_1053970
  simp only [CollatzResearch.WordTrace]
  refine ⟨9610360997913542147569841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25627629327769445726852909 9610360997913542147569841)
  ·
    refine ⟨7207770748435156610677381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9610360997913542147569841 7207770748435156610677381)
    ·
      refine ⟨1351457015331591864502009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7207770748435156610677381 1351457015331591864502009)
      ·
        refine ⟨1013592761498693898376507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1351457015331591864502009 1013592761498693898376507)
        ·
          refine ⟨1520389142248040847564761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1013592761498693898376507 1520389142248040847564761)
          ·
            refine ⟨1140291856686030635673571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1520389142248040847564761 1140291856686030635673571)
            ·
              refine ⟨1710437785029045953510357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140291856686030635673571 1710437785029045953510357)
              ·
                refine ⟨40088385586618264535399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1710437785029045953510357 40088385586618264535399)
                ·
                  rfl

theorem cell22_1053970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 7].length) (baseStart_1053970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1053970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1053970 prefixEnd_1053970 := by exact prefixLift 1053970
  have htrace : WordTrace (prefixWord ++ tailWord_1053970) baseStart_1053970 baseEnd_1053970 := by
    simpa [prefixWord, tailWord_1053970, baseEnd_1053970] using wordTrace_append hprefix tailTrace_1053970
  have hstable : (prefixWord ++ tailWord_1053970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1053970).length < 2 ^ (prefixWord ++ tailWord_1053970).sum := by decide
  have hdescent : baseEnd_1053970 < baseStart_1053970 := by decide
  rcases family_descends (prefixWord ++ tailWord_1053970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054041 : List Nat := [1, 2, 1, 2, 2, 2, 5, 1, 1, 5]
def baseStart_1054041 : Nat := 118140960795 + 1054041 * 2 ^ 59
def prefixEnd_1054041 : Nat := 4983230072969 + 3 ^ 40 * 1054041 * 2
def baseEnd_1054041 : Nat := 360819775030543862293373

theorem tailTrace_1054041 : CollatzResearch.WordTrace tailWord_1054041 prefixEnd_1054041 360819775030543862293373 := by
  unfold tailWord_1054041
  simp only [CollatzResearch.WordTrace]
  refine ⟨38444033574396947716113977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25629355716264631810742651 38444033574396947716113977)
  ·
    refine ⟨28833025180797710787085483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38444033574396947716113977 28833025180797710787085483)
    ·
      refine ⟨43249537771196566180628225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28833025180797710787085483 43249537771196566180628225)
      ·
        refine ⟨32437153328397424635471169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43249537771196566180628225 32437153328397424635471169)
        ·
          refine ⟨24327864996298068476603377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32437153328397424635471169 24327864996298068476603377)
          ·
            refine ⟨18245898747223551357452533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24327864996298068476603377 18245898747223551357452533)
            ·
              refine ⟨1710553007552207939761175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 18245898747223551357452533 1710553007552207939761175)
              ·
                refine ⟨2565829511328311909641763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1710553007552207939761175 2565829511328311909641763)
                ·
                  refine ⟨3848744266992467864462645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2565829511328311909641763 3848744266992467864462645)
                  ·
                    refine ⟨360819775030543862293373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3848744266992467864462645 360819775030543862293373)
                    ·
                      rfl

theorem cell22_1054041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 5, 1, 1, 5].length) (baseStart_1054041 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054041 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054041 prefixEnd_1054041 := by exact prefixLift 1054041
  have htrace : WordTrace (prefixWord ++ tailWord_1054041) baseStart_1054041 baseEnd_1054041 := by
    simpa [prefixWord, tailWord_1054041, baseEnd_1054041] using wordTrace_append hprefix tailTrace_1054041
  have hstable : (prefixWord ++ tailWord_1054041).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054041).length < 2 ^ (prefixWord ++ tailWord_1054041).sum := by decide
  have hdescent : baseEnd_1054041 < baseStart_1054041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054060 : List Nat := [2, 2, 1, 1, 5, 3, 1, 3, 4]
def baseStart_1054060 : Nat := 118140960795 + 1054060 * 2 ^ 59
def prefixEnd_1054060 : Nat := 4983230072969 + 3 ^ 40 * 1054060 * 2
def baseEnd_1054060 : Nat := 120275426372944715356105

theorem tailTrace_1054060 : CollatzResearch.WordTrace tailWord_1054060 prefixEnd_1054060 120275426372944715356105 := by
  unfold tailWord_1054060
  simp only [CollatzResearch.WordTrace]
  refine ⟨19222363280664056980527817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25629817707552075974037089 19222363280664056980527817)
  ·
    refine ⟨14416772460498042735395863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19222363280664056980527817 14416772460498042735395863)
    ·
      refine ⟨21625158690747064103093795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14416772460498042735395863 21625158690747064103093795)
      ·
        refine ⟨32437738036120596154640693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21625158690747064103093795 32437738036120596154640693)
        ·
          refine ⟨3041037940886305889497565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 32437738036120596154640693 3041037940886305889497565)
          ·
            refine ⟨1140389227832364708561587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3041037940886305889497565 1140389227832364708561587)
            ·
              refine ⟨1710583841748547062842381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140389227832364708561587 1710583841748547062842381)
              ·
                refine ⟨641468940655705148565893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1710583841748547062842381 641468940655705148565893)
                ·
                  refine ⟨120275426372944715356105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641468940655705148565893 120275426372944715356105)
                  ·
                    rfl

theorem cell22_1054060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 3, 1, 3, 4].length) (baseStart_1054060 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054060 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054060 prefixEnd_1054060 := by exact prefixLift 1054060
  have htrace : WordTrace (prefixWord ++ tailWord_1054060) baseStart_1054060 baseEnd_1054060 := by
    simpa [prefixWord, tailWord_1054060, baseEnd_1054060] using wordTrace_append hprefix tailTrace_1054060
  have hstable : (prefixWord ++ tailWord_1054060).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054060).length < 2 ^ (prefixWord ++ tailWord_1054060).sum := by decide
  have hdescent : baseEnd_1054060 < baseStart_1054060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054133 : List Nat := [1, 3, 3, 2, 2, 1, 1, 4, 5]
def baseStart_1054133 : Nat := 118140960795 + 1054133 * 2 ^ 59
def prefixEnd_1054133 : Nat := 4983230072969 + 3 ^ 40 * 1054133 * 2
def baseEnd_1054133 : Nat := 120283756170228762997697

theorem tailTrace_1054133 : CollatzResearch.WordTrace tailWord_1054133 prefixEnd_1054133 120283756170228762997697 := by
  unfold tailWord_1054133
  simp only [CollatzResearch.WordTrace]
  refine ⟨38447389090063647428463053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25631592726709098285642035 38447389090063647428463053)
  ·
    refine ⟨14417770908773867785673645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38447389090063647428463053 14417770908773867785673645)
    ·
      refine ⟨5406664090790200419627617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14417770908773867785673645 5406664090790200419627617)
      ·
        refine ⟨4054998068092650314720713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5406664090790200419627617 4054998068092650314720713)
        ·
          refine ⟨3041248551069487736040535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4054998068092650314720713 3041248551069487736040535)
          ·
            refine ⟨4561872826604231604060803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041248551069487736040535 4561872826604231604060803)
            ·
              refine ⟨6842809239906347406091205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561872826604231604060803 6842809239906347406091205)
              ·
                refine ⟨1283026732482440138642101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6842809239906347406091205 1283026732482440138642101)
                ·
                  refine ⟨120283756170228762997697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283026732482440138642101 120283756170228762997697)
                  ·
                    rfl

theorem cell22_1054133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 4, 5].length) (baseStart_1054133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054133 prefixEnd_1054133 := by exact prefixLift 1054133
  have htrace : WordTrace (prefixWord ++ tailWord_1054133) baseStart_1054133 baseEnd_1054133 := by
    simpa [prefixWord, tailWord_1054133, baseEnd_1054133] using wordTrace_append hprefix tailTrace_1054133
  have hstable : (prefixWord ++ tailWord_1054133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054133).length < 2 ^ (prefixWord ++ tailWord_1054133).sum := by decide
  have hdescent : baseEnd_1054133 < baseStart_1054133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054137 : List Nat := [1, 2, 1, 4, 4, 1, 1, 4, 1, 3]
def baseStart_1054137 : Nat := 118140960795 + 1054137 * 2 ^ 59
def prefixEnd_1054137 : Nat := 4983230072969 + 3 ^ 40 * 1054137 * 2
def baseEnd_1054137 : Nat := 360852637792431611893079

theorem tailTrace_1054137 : CollatzResearch.WordTrace tailWord_1054137 prefixEnd_1054137 360852637792431611893079 := by
  unfold tailWord_1054137
  simp only [CollatzResearch.WordTrace]
  refine ⟨38447534982049156111608665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25631689988032770741072443 38447534982049156111608665)
  ·
    refine ⟨28835651236536867083706499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38447534982049156111608665 28835651236536867083706499)
    ·
      refine ⟨43253476854805300625559749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28835651236536867083706499 43253476854805300625559749)
      ·
        refine ⟨8110026910275993867292453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43253476854805300625559749 8110026910275993867292453)
        ·
          refine ⟨1520630045676748850117335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8110026910275993867292453 1520630045676748850117335)
          ·
            refine ⟨2280945068515123275176003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1520630045676748850117335 2280945068515123275176003)
            ·
              refine ⟨3421417602772684912764005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2280945068515123275176003 3421417602772684912764005)
              ·
                refine ⟨641515800519878421143251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3421417602772684912764005 641515800519878421143251)
                ·
                  refine ⟨962273700779817631714877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641515800519878421143251 962273700779817631714877)
                  ·
                    refine ⟨360852637792431611893079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962273700779817631714877 360852637792431611893079)
                    ·
                      rfl

theorem cell22_1054137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 1, 1, 4, 1, 3].length) (baseStart_1054137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054137 prefixEnd_1054137 := by exact prefixLift 1054137
  have htrace : WordTrace (prefixWord ++ tailWord_1054137) baseStart_1054137 baseEnd_1054137 := by
    simpa [prefixWord, tailWord_1054137, baseEnd_1054137] using wordTrace_append hprefix tailTrace_1054137
  have hstable : (prefixWord ++ tailWord_1054137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054137).length < 2 ^ (prefixWord ++ tailWord_1054137).sum := by decide
  have hdescent : baseEnd_1054137 < baseStart_1054137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054148 : List Nat := [2, 3, 3, 2, 1, 1, 1, 1, 1, 7]
def baseStart_1054148 : Nat := 118140960795 + 1054148 * 2 ^ 59
def prefixEnd_1054148 : Nat := 4983230072969 + 3 ^ 40 * 1054148 * 2
def baseEnd_1054148 : Nat := 360856403317231249868045

theorem tailTrace_1054148 : CollatzResearch.WordTrace tailWord_1054148 prefixEnd_1054148 360856403317231249868045 := by
  unfold tailWord_1054148
  simp only [CollatzResearch.WordTrace]
  refine ⟨19223968092504652495129549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25631957456672869993506065 19223968092504652495129549)
  ·
    refine ⟨7208988034689244685673581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19223968092504652495129549 7208988034689244685673581)
    ·
      refine ⟨2703370513008466757127593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7208988034689244685673581 2703370513008466757127593)
      ·
        refine ⟨2027527884756350067845695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2703370513008466757127593 2027527884756350067845695)
        ·
          refine ⟨3041291827134525101768543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2027527884756350067845695 3041291827134525101768543)
          ·
            refine ⟨4561937740701787652652815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3041291827134525101768543 4561937740701787652652815)
            ·
              refine ⟨6842906611052681478979223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4561937740701787652652815 6842906611052681478979223)
              ·
                refine ⟨10264359916579022218468835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6842906611052681478979223 10264359916579022218468835)
                ·
                  refine ⟨15396539874868533327703253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10264359916579022218468835 15396539874868533327703253)
                  ·
                    refine ⟨360856403317231249868045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15396539874868533327703253 360856403317231249868045)
                    ·
                      rfl

theorem cell22_1054148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 1, 1, 7].length) (baseStart_1054148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054148 prefixEnd_1054148 := by exact prefixLift 1054148
  have htrace : WordTrace (prefixWord ++ tailWord_1054148) baseStart_1054148 baseEnd_1054148 := by
    simpa [prefixWord, tailWord_1054148, baseEnd_1054148] using wordTrace_append hprefix tailTrace_1054148
  have hstable : (prefixWord ++ tailWord_1054148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054148).length < 2 ^ (prefixWord ++ tailWord_1054148).sum := by decide
  have hdescent : baseEnd_1054148 < baseStart_1054148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054176 : List Nat := [2, 1, 1, 3, 1, 1, 2, 3, 3, 5]
def baseStart_1054176 : Nat := 118140960795 + 1054176 * 2 ^ 59
def prefixEnd_1054176 : Nat := 4983230072969 + 3 ^ 40 * 1054176 * 2
def baseEnd_1054176 : Nat := 360865988289448510167959

theorem tailTrace_1054176 : CollatzResearch.WordTrace tailWord_1054176 prefixEnd_1054176 360865988289448510167959 := by
  unfold tailWord_1054176
  simp only [CollatzResearch.WordTrace]
  refine ⟨19224478714453932886139191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25632638285938577181518921 19224478714453932886139191)
  ·
    refine ⟨28836718071680899329208787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19224478714453932886139191 28836718071680899329208787)
    ·
      refine ⟨43255077107521348993813181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28836718071680899329208787 43255077107521348993813181)
      ·
        refine ⟨16220653915320505872679943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43255077107521348993813181 16220653915320505872679943)
        ·
          refine ⟨24330980872980758809019915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16220653915320505872679943 24330980872980758809019915)
          ·
            refine ⟨36496471309471138213529873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24330980872980758809019915 36496471309471138213529873)
            ·
              refine ⟨27372353482103353660147405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36496471309471138213529873 27372353482103353660147405)
              ·
                refine ⟨10264632555788757622555277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27372353482103353660147405 10264632555788757622555277)
                ·
                  refine ⟨3849237208420784108458229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10264632555788757622555277 3849237208420784108458229)
                  ·
                    refine ⟨360865988289448510167959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3849237208420784108458229 360865988289448510167959)
                    ·
                      rfl

theorem cell22_1054176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 2, 3, 3, 5].length) (baseStart_1054176 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054176 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054176 prefixEnd_1054176 := by exact prefixLift 1054176
  have htrace : WordTrace (prefixWord ++ tailWord_1054176) baseStart_1054176 baseEnd_1054176 := by
    simpa [prefixWord, tailWord_1054176, baseEnd_1054176] using wordTrace_append hprefix tailTrace_1054176
  have hstable : (prefixWord ++ tailWord_1054176).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054176).length < 2 ^ (prefixWord ++ tailWord_1054176).sum := by decide
  have hdescent : baseEnd_1054176 < baseStart_1054176 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054495 : List Nat := [1, 1, 2, 4, 2, 1, 2, 2, 1, 6]
def baseStart_1054495 : Nat := 118140960795 + 1054495 * 2 ^ 59
def prefixEnd_1054495 : Nat := 4983230072969 + 3 ^ 40 * 1054495 * 2
def baseEnd_1054495 : Nat := 360975188508638011441981

theorem tailTrace_1054495 : CollatzResearch.WordTrace tailWord_1054495 prefixEnd_1054495 360975188508638011441981 := by
  unfold tailWord_1054495
  simp only [CollatzResearch.WordTrace]
  refine ⟨38460592314752183253140939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25640394876501455502093959 38460592314752183253140939)
  ·
    refine ⟨57690888472128274879711409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38460592314752183253140939 57690888472128274879711409)
    ·
      refine ⟨43268166354096206159783557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57690888472128274879711409 43268166354096206159783557)
      ·
        refine ⟨8112781191393038654959417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43268166354096206159783557 8112781191393038654959417)
        ·
          refine ⟨6084585893544778991219563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8112781191393038654959417 6084585893544778991219563)
          ·
            refine ⟨9126878840317168486829345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6084585893544778991219563 9126878840317168486829345)
            ·
              refine ⟨6845159130237876365122009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9126878840317168486829345 6845159130237876365122009)
              ·
                refine ⟨5133869347678407273841507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6845159130237876365122009 5133869347678407273841507)
                ·
                  refine ⟨7700804021517610910762261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5133869347678407273841507 7700804021517610910762261)
                  ·
                    refine ⟨360975188508638011441981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7700804021517610910762261 360975188508638011441981)
                    ·
                      rfl

theorem cell22_1054495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 2, 2, 1, 6].length) (baseStart_1054495 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054495 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054495 prefixEnd_1054495 := by exact prefixLift 1054495
  have htrace : WordTrace (prefixWord ++ tailWord_1054495) baseStart_1054495 baseEnd_1054495 := by
    simpa [prefixWord, tailWord_1054495, baseEnd_1054495] using wordTrace_append hprefix tailTrace_1054495
  have hstable : (prefixWord ++ tailWord_1054495).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054495).length < 2 ^ (prefixWord ++ tailWord_1054495).sum := by decide
  have hdescent : baseEnd_1054495 < baseStart_1054495 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054497 : List Nat := [1, 2, 3, 2, 1, 4, 2, 1, 1, 5]
def baseStart_1054497 : Nat := 118140960795 + 1054497 * 2 ^ 59
def prefixEnd_1054497 : Nat := 4983230072969 + 3 ^ 40 * 1054497 * 2
def baseEnd_1054497 : Nat := 360975873149510672891975

theorem tailTrace_1054497 : CollatzResearch.WordTrace tailWord_1054497 prefixEnd_1054497 360975873149510672891975 := by
  unfold tailWord_1054497
  simp only [CollatzResearch.WordTrace]
  refine ⟨38460665260744937594713745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25640443507163291729809163 38460665260744937594713745)
  ·
    refine ⟨28845498945558703196035309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38460665260744937594713745 28845498945558703196035309)
    ·
      refine ⟨10817062104584513698513241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28845498945558703196035309 10817062104584513698513241)
      ·
        refine ⟨8112796578438385273884931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10817062104584513698513241 8112796578438385273884931)
        ·
          refine ⟨12169194867657577910827397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8112796578438385273884931 12169194867657577910827397)
          ·
            refine ⟨2281724037685795858280137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 12169194867657577910827397 2281724037685795858280137)
            ·
              refine ⟨1711293028264346893710103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281724037685795858280137 1711293028264346893710103)
              ·
                refine ⟨2566939542396520340565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711293028264346893710103 2566939542396520340565155)
                ·
                  refine ⟨3850409313594780510847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2566939542396520340565155 3850409313594780510847733)
                  ·
                    refine ⟨360975873149510672891975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3850409313594780510847733 360975873149510672891975)
                    ·
                      rfl

theorem cell22_1054497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 1, 1, 5].length) (baseStart_1054497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054497 prefixEnd_1054497 := by exact prefixLift 1054497
  have htrace : WordTrace (prefixWord ++ tailWord_1054497) baseStart_1054497 baseEnd_1054497 := by
    simpa [prefixWord, tailWord_1054497, baseEnd_1054497] using wordTrace_append hprefix tailTrace_1054497
  have hstable : (prefixWord ++ tailWord_1054497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054497).length < 2 ^ (prefixWord ++ tailWord_1054497).sum := by decide
  have hdescent : baseEnd_1054497 < baseStart_1054497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054516 : List Nat := [2, 5, 1, 1, 2, 2, 2, 3, 4]
def baseStart_1054516 : Nat := 118140960795 + 1054516 * 2 ^ 59
def prefixEnd_1054516 : Nat := 4983230072969 + 3 ^ 40 * 1054516 * 2
def baseEnd_1054516 : Nat := 120327459079266985555639

theorem tailTrace_1054516 : CollatzResearch.WordTrace tailWord_1054516 prefixEnd_1054516 120327459079266985555639 := by
  unfold tailWord_1054516
  simp only [CollatzResearch.WordTrace]
  refine ⟨19230679123838051919827701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25640905498450735893103601 19230679123838051919827701)
  ·
    refine ⟨1802876167859817367483847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19230679123838051919827701 1802876167859817367483847)
    ·
      refine ⟨2704314251789726051225771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1802876167859817367483847 2704314251789726051225771)
      ·
        refine ⟨4056471377684589076838657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2704314251789726051225771 4056471377684589076838657)
        ·
          refine ⟨3042353533263441807628993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4056471377684589076838657 3042353533263441807628993)
          ·
            refine ⟨2281765149947581355721745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3042353533263441807628993 2281765149947581355721745)
            ·
              refine ⟨1711323862460686016791309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2281765149947581355721745 1711323862460686016791309)
              ·
                refine ⟨641746448422757256296741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711323862460686016791309 641746448422757256296741)
                ·
                  refine ⟨120327459079266985555639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641746448422757256296741 120327459079266985555639)
                  ·
                    rfl

theorem cell22_1054516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 2, 2, 3, 4].length) (baseStart_1054516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054516 prefixEnd_1054516 := by exact prefixLift 1054516
  have htrace : WordTrace (prefixWord ++ tailWord_1054516) baseStart_1054516 baseEnd_1054516 := by
    simpa [prefixWord, tailWord_1054516, baseEnd_1054516] using wordTrace_append hprefix tailTrace_1054516
  have hstable : (prefixWord ++ tailWord_1054516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054516).length < 2 ^ (prefixWord ++ tailWord_1054516).sum := by decide
  have hdescent : baseEnd_1054516 < baseStart_1054516 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054518 : List Nat := [5, 1, 2, 2, 1, 3, 2, 1, 1, 4]
def baseStart_1054518 : Nat := 118140960795 + 1054518 * 2 ^ 59
def prefixEnd_1054518 : Nat := 4983230072969 + 3 ^ 40 * 1054518 * 2
def baseEnd_1054518 : Nat := 360983061878673618116911

theorem tailTrace_1054518 : CollatzResearch.WordTrace tailWord_1054518 prefixEnd_1054518 360983061878673618116911 := by
  unfold tailWord_1054518
  simp only [CollatzResearch.WordTrace]
  refine ⟨2403839449604303636326763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25640954129112572120818805 2403839449604303636326763)
  ·
    refine ⟨3605759174406455454490145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2403839449604303636326763 3605759174406455454490145)
    ·
      refine ⟨2704319380804841590867609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3605759174406455454490145 2704319380804841590867609)
      ·
        refine ⟨2028239535603631193150707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2704319380804841590867609 2028239535603631193150707)
        ·
          refine ⟨3042359303405446789726061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2028239535603631193150707 3042359303405446789726061)
          ·
            refine ⟨1140884738777042546147273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3042359303405446789726061 1140884738777042546147273)
            ·
              refine ⟨855663554082781909610455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1140884738777042546147273 855663554082781909610455)
              ·
                refine ⟨1283495331124172864415683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 855663554082781909610455 1283495331124172864415683)
                ·
                  refine ⟨1925242996686259296623525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283495331124172864415683 1925242996686259296623525)
                  ·
                    refine ⟨360983061878673618116911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925242996686259296623525 360983061878673618116911)
                    ·
                      rfl

theorem cell22_1054518_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 1, 1, 4].length) (baseStart_1054518 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054518 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054518 prefixEnd_1054518 := by exact prefixLift 1054518
  have htrace : WordTrace (prefixWord ++ tailWord_1054518) baseStart_1054518 baseEnd_1054518 := by
    simpa [prefixWord, tailWord_1054518, baseEnd_1054518] using wordTrace_append hprefix tailTrace_1054518
  have hstable : (prefixWord ++ tailWord_1054518).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054518).length < 2 ^ (prefixWord ++ tailWord_1054518).sum := by decide
  have hdescent : baseEnd_1054518 < baseStart_1054518 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054518) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054593 : List Nat := [1, 2, 4, 4, 1, 2, 1, 1, 3, 3]
def baseStart_1054593 : Nat := 118140960795 + 1054593 * 2 ^ 59
def prefixEnd_1054593 : Nat := 4983230072969 + 3 ^ 40 * 1054593 * 2
def baseEnd_1054593 : Nat := 361008735911398422491681

theorem tailTrace_1054593 : CollatzResearch.WordTrace tailWord_1054593 prefixEnd_1054593 361008735911398422491681 := by
  unfold tailWord_1054593
  simp only [CollatzResearch.WordTrace]
  refine ⟨38464166668397145990208433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25642777778931430660138955 38464166668397145990208433)
  ·
    refine ⟨28848125001297859492656325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38464166668397145990208433 28848125001297859492656325)
    ·
      refine ⟨5409023437743348654873061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28848125001297859492656325 5409023437743348654873061)
      ·
        refine ⟨1014191894576877872788699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5409023437743348654873061 1014191894576877872788699)
        ·
          refine ⟨1521287841865316809183049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014191894576877872788699 1521287841865316809183049)
          ·
            refine ⟨1140965881398987606887287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521287841865316809183049 1140965881398987606887287)
            ·
              refine ⟨1711448822098481410330931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1140965881398987606887287 1711448822098481410330931)
              ·
                refine ⟨2567173233147722115496397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711448822098481410330931 2567173233147722115496397)
                ·
                  refine ⟨962689962430395793311149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2567173233147722115496397 962689962430395793311149)
                  ·
                    refine ⟨361008735911398422491681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962689962430395793311149 361008735911398422491681)
                    ·
                      rfl

theorem cell22_1054593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 2, 1, 1, 3, 3].length) (baseStart_1054593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054593 prefixEnd_1054593 := by exact prefixLift 1054593
  have htrace : WordTrace (prefixWord ++ tailWord_1054593) baseStart_1054593 baseEnd_1054593 := by
    simpa [prefixWord, tailWord_1054593, baseEnd_1054593] using wordTrace_append hprefix tailTrace_1054593
  have hstable : (prefixWord ++ tailWord_1054593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054593).length < 2 ^ (prefixWord ++ tailWord_1054593).sum := by decide
  have hdescent : baseEnd_1054593 < baseStart_1054593 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054606 : List Nat := [4, 1, 1, 5, 1, 1, 1, 3, 5]
def baseStart_1054606 : Nat := 118140960795 + 1054606 * 2 ^ 59
def prefixEnd_1054606 : Nat := 4983230072969 + 3 ^ 40 * 1054606 * 2
def baseEnd_1054606 : Nat := 120337728692356907305547

theorem tailTrace_1054606 : CollatzResearch.WordTrace tailWord_1054606 prefixEnd_1054606 120337728692356907305547 := by
  unfold tailWord_1054606
  simp only [CollatzResearch.WordTrace]
  refine ⟨4808080102168756151303959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25643093878233366140287781 4808080102168756151303959)
  ·
    refine ⟨7212120153253134226955939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4808080102168756151303959 7212120153253134226955939)
    ·
      refine ⟨10818180229879701340433909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7212120153253134226955939 10818180229879701340433909)
      ·
        refine ⟨1014204396551222000665679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10818180229879701340433909 1014204396551222000665679)
        ·
          refine ⟨1521306594826833000998519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014204396551222000665679 1521306594826833000998519)
          ·
            refine ⟨2281959892240249501497779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1521306594826833000998519 2281959892240249501497779)
            ·
              refine ⟨3422939838360374252246669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2281959892240249501497779 3422939838360374252246669)
              ·
                refine ⟨1283602439385140344592501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3422939838360374252246669 1283602439385140344592501)
                ·
                  refine ⟨120337728692356907305547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1283602439385140344592501 120337728692356907305547)
                  ·
                    rfl

theorem cell22_1054606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 3, 5].length) (baseStart_1054606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054606 prefixEnd_1054606 := by exact prefixLift 1054606
  have htrace : WordTrace (prefixWord ++ tailWord_1054606) baseStart_1054606 baseEnd_1054606 := by
    simpa [prefixWord, tailWord_1054606, baseEnd_1054606] using wordTrace_append hprefix tailTrace_1054606
  have hstable : (prefixWord ++ tailWord_1054606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054606).length < 2 ^ (prefixWord ++ tailWord_1054606).sum := by decide
  have hdescent : baseEnd_1054606 < baseStart_1054606 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054644 : List Nat := [2, 5, 2, 1, 3, 1, 2, 2, 1, 3]
def baseStart_1054644 : Nat := 118140960795 + 1054644 * 2 ^ 59
def prefixEnd_1054644 : Nat := 4983230072969 + 3 ^ 40 * 1054644 * 2
def baseEnd_1054644 : Nat := 361026194253651289466525

theorem tailTrace_1054644 : CollatzResearch.WordTrace tailWord_1054644 prefixEnd_1054644 361026194253651289466525 := by
  unfold tailWord_1054644
  simp only [CollatzResearch.WordTrace]
  refine ⟨19233013395606190850157493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25644017860808254466876657 19233013395606190850157493)
  ·
    refine ⟨1803095005838080392202265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19233013395606190850157493 1803095005838080392202265)
    ·
      refine ⟨1352321254378560294151699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1803095005838080392202265 1352321254378560294151699)
      ·
        refine ⟨2028481881567840441227549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352321254378560294151699 2028481881567840441227549)
        ·
          refine ⟨760680705587940165460331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2028481881567840441227549 760680705587940165460331)
          ·
            refine ⟨1141021058381910248190497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760680705587940165460331 1141021058381910248190497)
            ·
              refine ⟨855765793786432686142873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1141021058381910248190497 855765793786432686142873)
              ·
                refine ⟨641824345339824514607155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 855765793786432686142873 641824345339824514607155)
                ·
                  refine ⟨962736518009736771910733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641824345339824514607155 962736518009736771910733)
                  ·
                    refine ⟨361026194253651289466525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962736518009736771910733 361026194253651289466525)
                    ·
                      rfl

theorem cell22_1054644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 3, 1, 2, 2, 1, 3].length) (baseStart_1054644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054644 prefixEnd_1054644 := by exact prefixLift 1054644
  have htrace : WordTrace (prefixWord ++ tailWord_1054644) baseStart_1054644 baseEnd_1054644 := by
    simpa [prefixWord, tailWord_1054644, baseEnd_1054644] using wordTrace_append hprefix tailTrace_1054644
  have hstable : (prefixWord ++ tailWord_1054644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054644).length < 2 ^ (prefixWord ++ tailWord_1054644).sum := by decide
  have hdescent : baseEnd_1054644 < baseStart_1054644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054681 : List Nat := [1, 2, 1, 2, 6, 2, 1, 1, 2, 4]
def baseStart_1054681 : Nat := 118140960795 + 1054681 * 2 ^ 59
def prefixEnd_1054681 : Nat := 4983230072969 + 3 ^ 40 * 1054681 * 2
def baseEnd_1054681 : Nat := 361038860109795526291411

theorem tailTrace_1054681 : CollatzResearch.WordTrace tailWord_1054681 prefixEnd_1054681 361038860109795526291411 := by
  unfold tailWord_1054681
  simp only [CollatzResearch.WordTrace]
  refine ⟨38467376292078337019411897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25644917528052224679607931 38467376292078337019411897)
  ·
    refine ⟨28850532219058752764558923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38467376292078337019411897 28850532219058752764558923)
    ·
      refine ⟨43275798328588129146838385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28850532219058752764558923 43275798328588129146838385)
      ·
        refine ⟨32456848746441096860128789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43275798328588129146838385 32456848746441096860128789)
        ·
          refine ⟨1521414784989426415318537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32456848746441096860128789 1521414784989426415318537)
          ·
            refine ⟨1141061088742069811488903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1521414784989426415318537 1141061088742069811488903)
            ·
              refine ⟨1711591633113104717233355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141061088742069811488903 1711591633113104717233355)
              ·
                refine ⟨2567387449669657075850033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711591633113104717233355 2567387449669657075850033)
                ·
                  refine ⟨1925540587252242806887525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2567387449669657075850033 1925540587252242806887525)
                  ·
                    refine ⟨361038860109795526291411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925540587252242806887525 361038860109795526291411)
                    ·
                      rfl

theorem cell22_1054681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 1, 2, 4].length) (baseStart_1054681 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054681 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054681 prefixEnd_1054681 := by exact prefixLift 1054681
  have htrace : WordTrace (prefixWord ++ tailWord_1054681) baseStart_1054681 baseEnd_1054681 := by
    simpa [prefixWord, tailWord_1054681, baseEnd_1054681] using wordTrace_append hprefix tailTrace_1054681
  have hstable : (prefixWord ++ tailWord_1054681).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054681).length < 2 ^ (prefixWord ++ tailWord_1054681).sum := by decide
  have hdescent : baseEnd_1054681 < baseStart_1054681 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054767 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 5, 5]
def baseStart_1054767 : Nat := 118140960795 + 1054767 * 2 ^ 59
def prefixEnd_1054767 : Nat := 4983230072969 + 3 ^ 40 * 1054767 * 2
def baseEnd_1054767 : Nat := 361068299667319968641147

theorem tailTrace_1054767 : CollatzResearch.WordTrace tailWord_1054767 prefixEnd_1054767 361068299667319968641147 := by
  unfold tailWord_1054767
  simp only [CollatzResearch.WordTrace]
  refine ⟨38470512969766773707042555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25647008646511182471361703 38470512969766773707042555)
  ·
    refine ⟨57705769454650160560563833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38470512969766773707042555 57705769454650160560563833)
    ·
      refine ⟨43279327090987620420422875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57705769454650160560563833 43279327090987620420422875)
      ·
        refine ⟨64918990636481430630634313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43279327090987620420422875 64918990636481430630634313)
        ·
          refine ⟨48689242977361072972975735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64918990636481430630634313 48689242977361072972975735)
          ·
            refine ⟨73033864466041609459463603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48689242977361072972975735 73033864466041609459463603)
            ·
              refine ⟨109550796699062414189195405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73033864466041609459463603 109550796699062414189195405)
              ·
                refine ⟨41081548762148405320948277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 109550796699062414189195405 41081548762148405320948277)
                ·
                  refine ⟨3851395196451412998838901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 41081548762148405320948277 3851395196451412998838901)
                  ·
                    refine ⟨361068299667319968641147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3851395196451412998838901 361068299667319968641147)
                    ·
                      rfl

theorem cell22_1054767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 5, 5].length) (baseStart_1054767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054767 prefixEnd_1054767 := by exact prefixLift 1054767
  have htrace : WordTrace (prefixWord ++ tailWord_1054767) baseStart_1054767 baseEnd_1054767 := by
    simpa [prefixWord, tailWord_1054767, baseEnd_1054767] using wordTrace_append hprefix tailTrace_1054767
  have hstable : (prefixWord ++ tailWord_1054767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054767).length < 2 ^ (prefixWord ++ tailWord_1054767).sum := by decide
  have hdescent : baseEnd_1054767 < baseStart_1054767 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054769 : List Nat := [1, 2, 2, 3, 1, 3, 3, 1, 6]
def baseStart_1054769 : Nat := 118140960795 + 1054769 * 2 ^ 59
def prefixEnd_1054769 : Nat := 4983230072969 + 3 ^ 40 * 1054769 * 2
def baseEnd_1054769 : Nat := 120356328102730876697047

theorem tailTrace_1054769 : CollatzResearch.WordTrace tailWord_1054769 prefixEnd_1054769 120356328102730876697047 := by
  unfold tailWord_1054769
  simp only [CollatzResearch.WordTrace]
  refine ⟨38470585915759528048615361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25647057277173018699076907 38470585915759528048615361)
  ·
    refine ⟨28852939436819646036461521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38470585915759528048615361 28852939436819646036461521)
    ·
      refine ⟨21639704577614734527346141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28852939436819646036461521 21639704577614734527346141)
      ·
        refine ⟨8114889216605525447754803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21639704577614734527346141 8114889216605525447754803)
        ·
          refine ⟨12172333824908288171632205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8114889216605525447754803 12172333824908288171632205)
          ·
            refine ⟨4564625184340608064362077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12172333824908288171632205 4564625184340608064362077)
            ·
              refine ⟨1711734444127728024135779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4564625184340608064362077 1711734444127728024135779)
              ·
                refine ⟨2567601666191592036203669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1711734444127728024135779 2567601666191592036203669)
                ·
                  refine ⟨120356328102730876697047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2567601666191592036203669 120356328102730876697047)
                  ·
                    rfl

theorem cell22_1054769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 1, 6].length) (baseStart_1054769 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054769 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054769 prefixEnd_1054769 := by exact prefixLift 1054769
  have htrace : WordTrace (prefixWord ++ tailWord_1054769) baseStart_1054769 baseEnd_1054769 := by
    simpa [prefixWord, tailWord_1054769, baseEnd_1054769] using wordTrace_append hprefix tailTrace_1054769
  have hstable : (prefixWord ++ tailWord_1054769).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054769).length < 2 ^ (prefixWord ++ tailWord_1054769).sum := by decide
  have hdescent : baseEnd_1054769 < baseStart_1054769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054904 : List Nat := [2, 1, 2, 1, 2, 1, 3, 4, 6]
def baseStart_1054904 : Nat := 118140960795 + 1054904 * 2 ^ 59
def prefixEnd_1054904 : Nat := 4983230072969 + 3 ^ 40 * 1054904 * 2
def baseEnd_1054904 : Nat := 120371732522365759321909

theorem tailTrace_1054904 : CollatzResearch.WordTrace tailWord_1054904 prefixEnd_1054904 120371732522365759321909 := by
  unfold tailWord_1054904
  simp only [CollatzResearch.WordTrace]
  refine ⟨19237754885135223052389883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25650339846846964069853177 19237754885135223052389883)
  ·
    refine ⟨28856632327702834578584825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19237754885135223052389883 28856632327702834578584825)
    ·
      refine ⟨21642474245777125933938619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28856632327702834578584825 21642474245777125933938619)
      ·
        refine ⟨32463711368665688900907929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21642474245777125933938619 32463711368665688900907929)
        ·
          refine ⟨24347783526499266675680947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32463711368665688900907929 24347783526499266675680947)
          ·
            refine ⟨36521675289748900013521421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24347783526499266675680947 36521675289748900013521421)
            ·
              refine ⟨13695628233655837505070533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36521675289748900013521421 13695628233655837505070533)
              ·
                refine ⟨2567930293810469532200725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13695628233655837505070533 2567930293810469532200725)
                ·
                  refine ⟨120371732522365759321909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2567930293810469532200725 120371732522365759321909)
                  ·
                    rfl

theorem cell22_1054904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 4, 6].length) (baseStart_1054904 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054904 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054904 prefixEnd_1054904 := by exact prefixLift 1054904
  have htrace : WordTrace (prefixWord ++ tailWord_1054904) baseStart_1054904 baseEnd_1054904 := by
    simpa [prefixWord, tailWord_1054904, baseEnd_1054904] using wordTrace_append hprefix tailTrace_1054904
  have hstable : (prefixWord ++ tailWord_1054904).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054904).length < 2 ^ (prefixWord ++ tailWord_1054904).sum := by decide
  have hdescent : baseEnd_1054904 < baseStart_1054904 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054906 : List Nat := [3, 1, 1, 1, 2, 2, 3, 4, 1, 4]
def baseStart_1054906 : Nat := 118140960795 + 1054906 * 2 ^ 59
def prefixEnd_1054906 : Nat := 4983230072969 + 3 ^ 40 * 1054906 * 2
def baseEnd_1054906 : Nat := 361115882207969939415721

theorem tailTrace_1054906 : CollatzResearch.WordTrace tailWord_1054906 prefixEnd_1054906 361115882207969939415721 := by
  unfold tailWord_1054906
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618895679065800111588143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25650388477508800297568381 9618895679065800111588143)
  ·
    refine ⟨14428343518598700167382215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9618895679065800111588143 14428343518598700167382215)
    ·
      refine ⟨21642515277898050251073323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14428343518598700167382215 21642515277898050251073323)
      ·
        refine ⟨32463772916847075376609985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21642515277898050251073323 32463772916847075376609985)
        ·
          refine ⟨24347829687635306532457489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32463772916847075376609985 24347829687635306532457489)
          ·
            refine ⟨18260872265726479899343117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24347829687635306532457489 18260872265726479899343117)
            ·
              refine ⟨6847827099647429962253669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18260872265726479899343117 6847827099647429962253669)
              ·
                refine ⟨1283967581183893117922563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6847827099647429962253669 1283967581183893117922563)
                ·
                  refine ⟨1925951371775839676883845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1283967581183893117922563 1925951371775839676883845)
                  ·
                    refine ⟨361115882207969939415721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1925951371775839676883845 361115882207969939415721)
                    ·
                      rfl

theorem cell22_1054906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 4, 1, 4].length) (baseStart_1054906 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054906 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054906 prefixEnd_1054906 := by exact prefixLift 1054906
  have htrace : WordTrace (prefixWord ++ tailWord_1054906) baseStart_1054906 baseEnd_1054906 := by
    simpa [prefixWord, tailWord_1054906, baseEnd_1054906] using wordTrace_append hprefix tailTrace_1054906
  have hstable : (prefixWord ++ tailWord_1054906).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054906).length < 2 ^ (prefixWord ++ tailWord_1054906).sum := by decide
  have hdescent : baseEnd_1054906 < baseStart_1054906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054914 : List Nat := [3, 5, 1, 1, 1, 1, 3, 3, 1, 3]
def baseStart_1054914 : Nat := 118140960795 + 1054914 * 2 ^ 59
def prefixEnd_1054914 : Nat := 4983230072969 + 3 ^ 40 * 1054914 * 2
def baseEnd_1054914 : Nat := 361118620771460585215697

theorem tailTrace_1054914 : CollatzResearch.WordTrace tailWord_1054914 prefixEnd_1054914 361118620771460585215697 := by
  unfold tailWord_1054914
  simp only [CollatzResearch.WordTrace]
  refine ⟨9618968625058554453160949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25650583000156145208429197 9618968625058554453160949)
  ·
    refine ⟨901778308599239479983839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9618968625058554453160949 901778308599239479983839)
    ·
      refine ⟨1352667462898859219975759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 901778308599239479983839 1352667462898859219975759)
      ·
        refine ⟨2029001194348288829963639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1352667462898859219975759 2029001194348288829963639)
        ·
          refine ⟨3043501791522433244945459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029001194348288829963639 3043501791522433244945459)
          ·
            refine ⟨4565252687283649867418189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3043501791522433244945459 4565252687283649867418189)
            ·
              refine ⟨1711969757731368700281821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4565252687283649867418189 1711969757731368700281821)
              ·
                refine ⟨641988659149263262605683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1711969757731368700281821 641988659149263262605683)
                ·
                  refine ⟨962982988723894893908525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 641988659149263262605683 962982988723894893908525)
                  ·
                    refine ⟨361118620771460585215697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 962982988723894893908525 361118620771460585215697)
                    ·
                      rfl

theorem cell22_1054914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 3, 3, 1, 3].length) (baseStart_1054914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054914 prefixEnd_1054914 := by exact prefixLift 1054914
  have htrace : WordTrace (prefixWord ++ tailWord_1054914) baseStart_1054914 baseEnd_1054914 := by
    simpa [prefixWord, tailWord_1054914, baseEnd_1054914] using wordTrace_append hprefix tailTrace_1054914
  have hstable : (prefixWord ++ tailWord_1054914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054914).length < 2 ^ (prefixWord ++ tailWord_1054914).sum := by decide
  have hdescent : baseEnd_1054914 < baseStart_1054914 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054921 : List Nat := [1, 2, 1, 1, 2, 1, 1, 9, 4]
def baseStart_1054921 : Nat := 118140960795 + 1054921 * 2 ^ 59
def prefixEnd_1054921 : Nat := 4983230072969 + 3 ^ 40 * 1054921 * 2
def baseEnd_1054921 : Nat := 120373672338171633430225

theorem tailTrace_1054921 : CollatzResearch.WordTrace tailWord_1054921 prefixEnd_1054921 120373672338171633430225 := by
  unfold tailWord_1054921
  simp only [CollatzResearch.WordTrace]
  refine ⟨38476129811208858008148617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25650753207472572005432411 38476129811208858008148617)
  ·
    refine ⟨28857097358406643506111463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38476129811208858008148617 28857097358406643506111463)
    ·
      refine ⟨43285646037609965259167195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28857097358406643506111463 43285646037609965259167195)
      ·
        refine ⟨64928469056414947888750793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43285646037609965259167195 64928469056414947888750793)
        ·
          refine ⟨48696351792311210916563095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64928469056414947888750793 48696351792311210916563095)
          ·
            refine ⟨73044527688466816374844643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48696351792311210916563095 73044527688466816374844643)
            ·
              refine ⟨109566791532700224562266965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 73044527688466816374844643 109566791532700224562266965)
              ·
                refine ⟨641992919136915378294533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 109566791532700224562266965 641992919136915378294533)
                ·
                  refine ⟨120373672338171633430225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 641992919136915378294533 120373672338171633430225)
                  ·
                    rfl

theorem cell22_1054921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 9, 4].length) (baseStart_1054921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054921 prefixEnd_1054921 := by exact prefixLift 1054921
  have htrace : WordTrace (prefixWord ++ tailWord_1054921) baseStart_1054921 baseEnd_1054921 := by
    simpa [prefixWord, tailWord_1054921, baseEnd_1054921] using wordTrace_append hprefix tailTrace_1054921
  have hstable : (prefixWord ++ tailWord_1054921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054921).length < 2 ^ (prefixWord ++ tailWord_1054921).sum := by decide
  have hdescent : baseEnd_1054921 < baseStart_1054921 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054957 : List Nat := [1, 5, 1, 2, 4, 1, 1, 2, 1, 4]
def baseStart_1054957 : Nat := 118140960795 + 1054957 * 2 ^ 59
def prefixEnd_1054957 : Nat := 4983230072969 + 3 ^ 40 * 1054957 * 2
def baseEnd_1054957 : Nat := 361133340550222806390565

theorem tailTrace_1054957 : CollatzResearch.WordTrace tailWord_1054957 prefixEnd_1054957 361133340550222806390565 := by
  unfold tailWord_1054957
  simp only [CollatzResearch.WordTrace]
  refine ⟨38477442839078436156459125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25651628559385624104306083 38477442839078436156459125)
  ·
    refine ⟨3607260266163603389668043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38477442839078436156459125 3607260266163603389668043)
    ·
      refine ⟨5410890399245405084502065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607260266163603389668043 5410890399245405084502065)
      ·
        refine ⟨4058167799434053813376549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5410890399245405084502065 4058167799434053813376549)
        ·
          refine ⟨760906462393885090008103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4058167799434053813376549 760906462393885090008103)
          ·
            refine ⟨1141359693590827635012155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 760906462393885090008103 1141359693590827635012155)
            ·
              refine ⟨1712039540386241452518233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141359693590827635012155 1712039540386241452518233)
              ·
                refine ⟨1284029655289681089388675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712039540386241452518233 1284029655289681089388675)
                ·
                  refine ⟨1926044482934521634083013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284029655289681089388675 1926044482934521634083013)
                  ·
                    refine ⟨361133340550222806390565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926044482934521634083013 361133340550222806390565)
                    ·
                      rfl

theorem cell22_1054957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 2, 1, 4].length) (baseStart_1054957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054957 prefixEnd_1054957 := by exact prefixLift 1054957
  have htrace : WordTrace (prefixWord ++ tailWord_1054957) baseStart_1054957 baseEnd_1054957 := by
    simpa [prefixWord, tailWord_1054957, baseEnd_1054957] using wordTrace_append hprefix tailTrace_1054957
  have hstable : (prefixWord ++ tailWord_1054957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054957).length < 2 ^ (prefixWord ++ tailWord_1054957).sum := by decide
  have hdescent : baseEnd_1054957 < baseStart_1054957 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054966 : List Nat := [5, 1, 1, 1, 1, 1, 4, 8]
def baseStart_1054966 : Nat := 118140960795 + 1054966 * 2 ^ 59
def prefixEnd_1054966 : Nat := 4983230072969 + 3 ^ 40 * 1054966 * 2
def baseEnd_1054966 : Nat := 40126269048238864768393

theorem tailTrace_1054966 : CollatzResearch.WordTrace tailWord_1054966 prefixEnd_1054966 40126269048238864768393 := by
  unfold tailWord_1054966
  simp only [CollatzResearch.WordTrace]
  refine ⟨2404860693502864418346047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25651847397363887129024501 2404860693502864418346047)
  ·
    refine ⟨3607291040254296627519071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2404860693502864418346047 3607291040254296627519071)
    ·
      refine ⟨5410936560381444941278607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3607291040254296627519071 5410936560381444941278607)
      ·
        refine ⟨8116404840572167411917911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5410936560381444941278607 8116404840572167411917911)
        ·
          refine ⟨12174607260858251117876867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8116404840572167411917911 12174607260858251117876867)
          ·
            refine ⟨18261910891287376676815301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12174607260858251117876867 18261910891287376676815301)
            ·
              refine ⟨3424108292116383126902869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18261910891287376676815301 3424108292116383126902869)
              ·
                refine ⟨40126269048238864768393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3424108292116383126902869 40126269048238864768393)
                ·
                  rfl

theorem cell22_1054966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 8].length) (baseStart_1054966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054966 prefixEnd_1054966 := by exact prefixLift 1054966
  have htrace : WordTrace (prefixWord ++ tailWord_1054966) baseStart_1054966 baseEnd_1054966 := by
    simpa [prefixWord, tailWord_1054966, baseEnd_1054966] using wordTrace_append hprefix tailTrace_1054966
  have hstable : (prefixWord ++ tailWord_1054966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054966).length < 2 ^ (prefixWord ++ tailWord_1054966).sum := by decide
  have hdescent : baseEnd_1054966 < baseStart_1054966 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054981 : List Nat := [1, 3, 1, 1, 2, 1, 2, 1, 7, 3]
def baseStart_1054981 : Nat := 118140960795 + 1054981 * 2 ^ 59
def prefixEnd_1054981 : Nat := 4983230072969 + 3 ^ 40 * 1054981 * 2
def baseEnd_1054981 : Nat := 361141556240694743790491

theorem tailTrace_1054981 : CollatzResearch.WordTrace tailWord_1054981 prefixEnd_1054981 361141556240694743790491 := by
  unfold tailWord_1054981
  simp only [CollatzResearch.WordTrace]
  refine ⟨38478318190991488255332797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25652212127327658836888531 38478318190991488255332797)
  ·
    refine ⟨14429369321621808095749799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38478318190991488255332797 14429369321621808095749799)
    ·
      refine ⟨21644053982432712143624699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14429369321621808095749799 21644053982432712143624699)
      ·
        refine ⟨32466080973649068215437049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21644053982432712143624699 32466080973649068215437049)
        ·
          refine ⟨24349560730236801161577787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32466080973649068215437049 24349560730236801161577787)
          ·
            refine ⟨36524341095355201742366681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24349560730236801161577787 36524341095355201742366681)
            ·
              refine ⟨27393255821516401306775011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36524341095355201742366681 27393255821516401306775011)
              ·
                refine ⟨41089883732274601960162517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27393255821516401306775011 41089883732274601960162517)
                ·
                  refine ⟨963044149975185983441309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 41089883732274601960162517 963044149975185983441309)
                  ·
                    refine ⟨361141556240694743790491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963044149975185983441309 361141556240694743790491)
                    ·
                      rfl

theorem cell22_1054981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 2, 1, 7, 3].length) (baseStart_1054981 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054981 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054981 prefixEnd_1054981 := by exact prefixLift 1054981
  have htrace : WordTrace (prefixWord ++ tailWord_1054981) baseStart_1054981 baseEnd_1054981 := by
    simpa [prefixWord, tailWord_1054981, baseEnd_1054981] using wordTrace_append hprefix tailTrace_1054981
  have hstable : (prefixWord ++ tailWord_1054981).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054981).length < 2 ^ (prefixWord ++ tailWord_1054981).sum := by decide
  have hdescent : baseEnd_1054981 < baseStart_1054981 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1054983 : List Nat := [1, 1, 4, 5, 2, 9]
def baseStart_1054983 : Nat := 118140960795 + 1054983 * 2 ^ 59
def prefixEnd_1054983 : Nat := 4983230072969 + 3 ^ 40 * 1054983 * 2
def baseEnd_1054983 : Nat := 4458546183723054385685

theorem tailTrace_1054983 : CollatzResearch.WordTrace tailWord_1054983 prefixEnd_1054983 4458546183723054385685 := by
  unfold tailWord_1054983
  simp only [CollatzResearch.WordTrace]
  refine ⟨38478391136984242596905603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25652260757989495064603735 38478391136984242596905603)
  ·
    refine ⟨57717586705476363895358405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38478391136984242596905603 57717586705476363895358405)
    ·
      refine ⟨10822047507276818230379701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57717586705476363895358405 10822047507276818230379701)
      ·
        refine ⟨1014566953807201709098097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10822047507276818230379701 1014566953807201709098097)
        ·
          refine ⟨760925215355401281823573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1014566953807201709098097 760925215355401281823573)
          ·
            refine ⟨4458546183723054385685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 760925215355401281823573 4458546183723054385685)
            ·
              rfl

theorem cell22_1054983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 9].length) (baseStart_1054983 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1054983 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1054983 prefixEnd_1054983 := by exact prefixLift 1054983
  have htrace : WordTrace (prefixWord ++ tailWord_1054983) baseStart_1054983 baseEnd_1054983 := by
    simpa [prefixWord, tailWord_1054983, baseEnd_1054983] using wordTrace_append hprefix tailTrace_1054983
  have hstable : (prefixWord ++ tailWord_1054983).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1054983).length < 2 ^ (prefixWord ++ tailWord_1054983).sum := by decide
  have hdescent : baseEnd_1054983 < baseStart_1054983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1054983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055011 : List Nat := [1, 1, 1, 4, 2, 2, 1, 5, 5]
def baseStart_1055011 : Nat := 118140960795 + 1055011 * 2 ^ 59
def prefixEnd_1055011 : Nat := 4983230072969 + 3 ^ 40 * 1055011 * 2
def baseEnd_1055011 : Nat := 120383941951261555180133

theorem tailTrace_1055011 : CollatzResearch.WordTrace tailWord_1055011 prefixEnd_1055011 120383941951261555180133 := by
  unfold tailWord_1055011
  simp only [CollatzResearch.WordTrace]
  refine ⟨38479412380882803378924887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25652941587255202252616591 38479412380882803378924887)
  ·
    refine ⟨57719118571324205068387331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38479412380882803378924887 57719118571324205068387331)
    ·
      refine ⟨86578677856986307602580997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57719118571324205068387331 86578677856986307602580997)
      ·
        refine ⟨16233502098184932675483937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86578677856986307602580997 16233502098184932675483937)
        ·
          refine ⟨12175126573638699506612953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16233502098184932675483937 12175126573638699506612953)
          ·
            refine ⟨9131344930229024629959715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12175126573638699506612953 9131344930229024629959715)
            ·
              refine ⟨13697017395343536944939573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9131344930229024629959715 13697017395343536944939573)
              ·
                refine ⟨1284095380813456588588085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13697017395343536944939573 1284095380813456588588085)
                ·
                  refine ⟨120383941951261555180133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1284095380813456588588085 120383941951261555180133)
                  ·
                    rfl

theorem cell22_1055011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 5, 5].length) (baseStart_1055011 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055011 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055011 prefixEnd_1055011 := by exact prefixLift 1055011
  have htrace : WordTrace (prefixWord ++ tailWord_1055011) baseStart_1055011 baseEnd_1055011 := by
    simpa [prefixWord, tailWord_1055011, baseEnd_1055011] using wordTrace_append hprefix tailTrace_1055011
  have hstable : (prefixWord ++ tailWord_1055011).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055011).length < 2 ^ (prefixWord ++ tailWord_1055011).sum := by decide
  have hdescent : baseEnd_1055011 < baseStart_1055011 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055056 : List Nat := [2, 1, 1, 1, 1, 6, 1, 3, 6]
def baseStart_1055056 : Nat := 118140960795 + 1055056 * 2 ^ 59
def prefixEnd_1055056 : Nat := 4983230072969 + 3 ^ 40 * 1055056 * 2
def baseEnd_1055056 : Nat := 120389076757806516055087

theorem tailTrace_1055056 : CollatzResearch.WordTrace tailWord_1055056 prefixEnd_1055056 120389076757806516055087 := by
  unfold tailWord_1055056
  simp only [CollatzResearch.WordTrace]
  refine ⟨19240526832859888032156511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25654035777146517376208681 19240526832859888032156511)
  ·
    refine ⟨28860790249289832048234767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19240526832859888032156511 28860790249289832048234767)
    ·
      refine ⟨43291185373934748072352151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28860790249289832048234767 43291185373934748072352151)
      ·
        refine ⟨64936778060902122108528227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43291185373934748072352151 64936778060902122108528227)
        ·
          refine ⟨97405167091353183162792341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64936778060902122108528227 97405167091353183162792341)
          ·
            refine ⟨4565867207407180460755891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 97405167091353183162792341 4565867207407180460755891)
            ·
              refine ⟨6848800811110770691133837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4565867207407180460755891 6848800811110770691133837)
              ·
                refine ⟨2568300304166539009175189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6848800811110770691133837 2568300304166539009175189)
                ·
                  refine ⟨120389076757806516055087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2568300304166539009175189 120389076757806516055087)
                  ·
                    rfl

theorem cell22_1055056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 3, 6].length) (baseStart_1055056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055056 prefixEnd_1055056 := by exact prefixLift 1055056
  have htrace : WordTrace (prefixWord ++ tailWord_1055056) baseStart_1055056 baseEnd_1055056 := by
    simpa [prefixWord, tailWord_1055056, baseEnd_1055056] using wordTrace_append hprefix tailTrace_1055056
  have hstable : (prefixWord ++ tailWord_1055056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055056).length < 2 ^ (prefixWord ++ tailWord_1055056).sum := by decide
  have hdescent : baseEnd_1055056 < baseStart_1055056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055088 : List Nat := [2, 1, 1, 1, 4, 3, 1, 2, 4, 3]
def baseStart_1055088 : Nat := 118140960795 + 1055088 * 2 ^ 59
def prefixEnd_1055088 : Nat := 4983230072969 + 3 ^ 40 * 1055088 * 2
def baseEnd_1055088 : Nat := 361178184527382131365163

theorem tailTrace_1055088 : CollatzResearch.WordTrace tailWord_1055088 prefixEnd_1055088 361178184527382131365163 := by
  unfold tailWord_1055088
  simp only [CollatzResearch.WordTrace]
  refine ⟨19241110400801922764738959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25654813867735897019651945 19241110400801922764738959)
  ·
    refine ⟨28861665601202884147108439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19241110400801922764738959 28861665601202884147108439)
    ·
      refine ⟨43292498401804326220662659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28861665601202884147108439 43292498401804326220662659)
      ·
        refine ⟨64938747602706489330993989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43292498401804326220662659 64938747602706489330993989)
        ·
          refine ⟨12176015175507466749561373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64938747602706489330993989 12176015175507466749561373)
          ·
            refine ⟨4566005690815300031085515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12176015175507466749561373 4566005690815300031085515)
            ·
              refine ⟨6849008536222950046628273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566005690815300031085515 6849008536222950046628273)
              ·
                refine ⟨5136756402167212534971205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6849008536222950046628273 5136756402167212534971205)
                ·
                  refine ⟨963141825406352350307101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5136756402167212534971205 963141825406352350307101)
                  ·
                    refine ⟨361178184527382131365163, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963141825406352350307101 361178184527382131365163)
                    ·
                      rfl

theorem cell22_1055088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 1, 2, 4, 3].length) (baseStart_1055088 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055088 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055088 prefixEnd_1055088 := by exact prefixLift 1055088
  have htrace : WordTrace (prefixWord ++ tailWord_1055088) baseStart_1055088 baseEnd_1055088 := by
    simpa [prefixWord, tailWord_1055088, baseEnd_1055088] using wordTrace_append hprefix tailTrace_1055088
  have hstable : (prefixWord ++ tailWord_1055088).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055088).length < 2 ^ (prefixWord ++ tailWord_1055088).sum := by decide
  have hdescent : baseEnd_1055088 < baseStart_1055088 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055090 : List Nat := [3, 2, 1, 2, 1, 3, 3, 3, 4]
def baseStart_1055090 : Nat := 118140960795 + 1055090 * 2 ^ 59
def prefixEnd_1055090 : Nat := 4983230072969 + 3 ^ 40 * 1055090 * 2
def baseEnd_1055090 : Nat := 120392956389418264271719

theorem tailTrace_1055090 : CollatzResearch.WordTrace tailWord_1055090 prefixEnd_1055090 120392956389418264271719 := by
  unfold tailWord_1055090
  simp only [CollatzResearch.WordTrace]
  refine ⟨9620573436899149967762681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25654862498397733247367149 9620573436899149967762681)
  ·
    refine ⟨7215430077674362475822011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9620573436899149967762681 7215430077674362475822011)
    ·
      refine ⟨10823145116511543713733017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215430077674362475822011 10823145116511543713733017)
      ·
        refine ⟨8117358837383657785299763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10823145116511543713733017 8117358837383657785299763)
        ·
          refine ⟨12176038256075486677949645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8117358837383657785299763 12176038256075486677949645)
          ·
            refine ⟨4566014346028307504231117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12176038256075486677949645 4566014346028307504231117)
            ·
              refine ⟨1712255379760615314086669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4566014346028307504231117 1712255379760615314086669)
              ·
                refine ⟨642095767410230742782501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712255379760615314086669 642095767410230742782501)
                ·
                  refine ⟨120392956389418264271719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642095767410230742782501 120392956389418264271719)
                  ·
                    rfl

theorem cell22_1055090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 3, 4].length) (baseStart_1055090 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055090 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055090 prefixEnd_1055090 := by exact prefixLift 1055090
  have htrace : WordTrace (prefixWord ++ tailWord_1055090) baseStart_1055090 baseEnd_1055090 := by
    simpa [prefixWord, tailWord_1055090, baseEnd_1055090] using wordTrace_append hprefix tailTrace_1055090
  have hstable : (prefixWord ++ tailWord_1055090).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055090).length < 2 ^ (prefixWord ++ tailWord_1055090).sum := by decide
  have hdescent : baseEnd_1055090 < baseStart_1055090 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055101 : List Nat := [1, 4, 1, 1, 2, 3, 10]
def baseStart_1055101 : Nat := 118140960795 + 1055101 * 2 ^ 59
def prefixEnd_1055101 : Nat := 4983230072969 + 3 ^ 40 * 1055101 * 2
def baseEnd_1055101 : Nat := 13377134618261275214449

theorem tailTrace_1055101 : CollatzResearch.WordTrace tailWord_1055101 prefixEnd_1055101 13377134618261275214449 := by
  unfold tailWord_1055101
  simp only [CollatzResearch.WordTrace]
  refine ⟨38482694950556748749701157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25655129967037832499800771 38482694950556748749701157)
  ·
    refine ⟨7215505303229390390568967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38482694950556748749701157 7215505303229390390568967)
    ·
      refine ⟨10823257954844085585853451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215505303229390390568967 10823257954844085585853451)
      ·
        refine ⟨16234886932266128378780177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10823257954844085585853451 16234886932266128378780177)
        ·
          refine ⟨12176165199199596284085133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16234886932266128378780177 12176165199199596284085133)
          ·
            refine ⟨4566061949699848606531925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12176165199199596284085133 4566061949699848606531925)
            ·
              refine ⟨13377134618261275214449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4566061949699848606531925 13377134618261275214449)
              ·
                rfl

theorem cell22_1055101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 10].length) (baseStart_1055101 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055101 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055101 prefixEnd_1055101 := by exact prefixLift 1055101
  have htrace : WordTrace (prefixWord ++ tailWord_1055101) baseStart_1055101 baseEnd_1055101 := by
    simpa [prefixWord, tailWord_1055101, baseEnd_1055101] using wordTrace_append hprefix tailTrace_1055101
  have hstable : (prefixWord ++ tailWord_1055101).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055101).length < 2 ^ (prefixWord ++ tailWord_1055101).sum := by decide
  have hdescent : baseEnd_1055101 < baseStart_1055101 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055105 : List Nat := [1, 2, 4, 3, 1, 1, 2, 1, 4, 3]
def baseStart_1055105 : Nat := 118140960795 + 1055105 * 2 ^ 59
def prefixEnd_1055105 : Nat := 4983230072969 + 3 ^ 40 * 1055105 * 2
def baseEnd_1055105 : Nat := 361184003974799753690111

theorem tailTrace_1055105 : CollatzResearch.WordTrace tailWord_1055105 prefixEnd_1055105 361184003974799753690111 := by
  unfold tailWord_1055105
  simp only [CollatzResearch.WordTrace]
  refine ⟨38482840842542257432846769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25655227228361504955231179 38482840842542257432846769)
  ·
    refine ⟨28862130631906693074635077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38482840842542257432846769 28862130631906693074635077)
    ·
      refine ⟨5411649493482504951494077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28862130631906693074635077 5411649493482504951494077)
      ·
        refine ⟨2029368560055939356810279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5411649493482504951494077 2029368560055939356810279)
        ·
          refine ⟨3044052840083909035215419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029368560055939356810279 3044052840083909035215419)
          ·
            refine ⟨4566079260125863552823129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044052840083909035215419 4566079260125863552823129)
            ·
              refine ⟨3424559445094397664617347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4566079260125863552823129 3424559445094397664617347)
              ·
                refine ⟨5136839167641596496926021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424559445094397664617347 5136839167641596496926021)
                ·
                  refine ⟨963157343932799343173629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5136839167641596496926021 963157343932799343173629)
                  ·
                    refine ⟨361184003974799753690111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963157343932799343173629 361184003974799753690111)
                    ·
                      rfl

theorem cell22_1055105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 2, 1, 4, 3].length) (baseStart_1055105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055105 prefixEnd_1055105 := by exact prefixLift 1055105
  have htrace : WordTrace (prefixWord ++ tailWord_1055105) baseStart_1055105 baseEnd_1055105 := by
    simpa [prefixWord, tailWord_1055105, baseEnd_1055105] using wordTrace_append hprefix tailTrace_1055105
  have hstable : (prefixWord ++ tailWord_1055105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055105).length < 2 ^ (prefixWord ++ tailWord_1055105).sum := by decide
  have hdescent : baseEnd_1055105 < baseStart_1055105 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055107 : List Nat := [1, 1, 1, 3, 6, 1, 3, 2, 4]
def baseStart_1055107 : Nat := 118140960795 + 1055107 * 2 ^ 59
def prefixEnd_1055107 : Nat := 4983230072969 + 3 ^ 40 * 1055107 * 2
def baseEnd_1055107 : Nat := 120394896205224138380035

theorem tailTrace_1055107 : CollatzResearch.WordTrace tailWord_1055107 prefixEnd_1055107 120394896205224138380035 := by
  unfold tailWord_1055107
  simp only [CollatzResearch.WordTrace]
  refine ⟨38482913788535011774419575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25655275859023341182946383 38482913788535011774419575)
  ·
    refine ⟨57724370682802517661629363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38482913788535011774419575 57724370682802517661629363)
    ·
      refine ⟨86586556024203776492444045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57724370682802517661629363 86586556024203776492444045)
      ·
        refine ⟨32469958509076416184666517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86586556024203776492444045 32469958509076416184666517)
        ·
          refine ⟨1522029305112957008656243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32469958509076416184666517 1522029305112957008656243)
          ·
            refine ⟨2283043957669435512984365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522029305112957008656243 2283043957669435512984365)
            ·
              refine ⟨856141484126038317369137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2283043957669435512984365 856141484126038317369137)
              ·
                refine ⟨642106113094528738026853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856141484126038317369137 642106113094528738026853)
                ·
                  refine ⟨120394896205224138380035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642106113094528738026853 120394896205224138380035)
                  ·
                    rfl

theorem cell22_1055107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 1, 3, 2, 4].length) (baseStart_1055107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055107 prefixEnd_1055107 := by exact prefixLift 1055107
  have htrace : WordTrace (prefixWord ++ tailWord_1055107) baseStart_1055107 baseEnd_1055107 := by
    simpa [prefixWord, tailWord_1055107, baseEnd_1055107] using wordTrace_append hprefix tailTrace_1055107
  have hstable : (prefixWord ++ tailWord_1055107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055107).length < 2 ^ (prefixWord ++ tailWord_1055107).sum := by decide
  have hdescent : baseEnd_1055107 < baseStart_1055107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055118 : List Nat := [4, 1, 1, 4, 1, 1, 1, 9]
def baseStart_1055118 : Nat := 118140960795 + 1055118 * 2 ^ 59
def prefixEnd_1055118 : Nat := 4983230072969 + 3 ^ 40 * 1055118 * 2
def baseEnd_1055118 : Nat := 40132050460052450346119

theorem tailTrace_1055118 : CollatzResearch.WordTrace tailWord_1055118 prefixEnd_1055118 40132050460052450346119 := by
  unfold tailWord_1055118
  simp only [CollatzResearch.WordTrace]
  refine ⟨4810414373936895081633751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 25655543327663440435380005 4810414373936895081633751)
  ·
    refine ⟨7215621560905342622450627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4810414373936895081633751 7215621560905342622450627)
    ·
      refine ⟨10823432341358013933675941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7215621560905342622450627 10823432341358013933675941)
      ·
        refine ⟨2029393564004627612564239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10823432341358013933675941 2029393564004627612564239)
        ·
          refine ⟨3044090346006941418846359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029393564004627612564239 3044090346006941418846359)
          ·
            refine ⟨4566135519010412128269539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3044090346006941418846359 4566135519010412128269539)
            ·
              refine ⟨6849203278515618192404309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4566135519010412128269539 6849203278515618192404309)
              ·
                refine ⟨40132050460052450346119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 6849203278515618192404309 40132050460052450346119)
                ·
                  rfl

theorem cell22_1055118_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 9].length) (baseStart_1055118 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055118 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055118 prefixEnd_1055118 := by exact prefixLift 1055118
  have htrace : WordTrace (prefixWord ++ tailWord_1055118) baseStart_1055118 baseEnd_1055118 := by
    simpa [prefixWord, tailWord_1055118, baseEnd_1055118] using wordTrace_append hprefix tailTrace_1055118
  have hstable : (prefixWord ++ tailWord_1055118).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055118).length < 2 ^ (prefixWord ++ tailWord_1055118).sum := by decide
  have hdescent : baseEnd_1055118 < baseStart_1055118 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055118) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055137 : List Nat := [1, 2, 3, 5, 1, 1, 2, 1, 2, 4]
def baseStart_1055137 : Nat := 118140960795 + 1055137 * 2 ^ 59
def prefixEnd_1055137 : Nat := 4983230072969 + 3 ^ 40 * 1055137 * 2
def baseEnd_1055137 : Nat := 361194958228762336890013

theorem tailTrace_1055137 : CollatzResearch.WordTrace tailWord_1055137 prefixEnd_1055137 361194958228762336890013 := by
  unfold tailWord_1055137
  simp only [CollatzResearch.WordTrace]
  refine ⟨38484007978426326898011665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656005318950884598674443 38484007978426326898011665)
  ·
    refine ⟨28863005983819745173508749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38484007978426326898011665 28863005983819745173508749)
    ·
      refine ⟨10823627243932404440065781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28863005983819745173508749 10823627243932404440065781)
      ·
        refine ⟨1014715054118662916256167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10823627243932404440065781 1014715054118662916256167)
        ·
          refine ⟨1522072581177994374384251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014715054118662916256167 1522072581177994374384251)
          ·
            refine ⟨2283108871766991561576377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522072581177994374384251 2283108871766991561576377)
            ·
              refine ⟨1712331653825243671182283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2283108871766991561576377 1712331653825243671182283)
              ·
                refine ⟨2568497480737865506773425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1712331653825243671182283 2568497480737865506773425)
                ·
                  refine ⟨1926373110553399130080069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2568497480737865506773425 1926373110553399130080069)
                  ·
                    refine ⟨361194958228762336890013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926373110553399130080069 361194958228762336890013)
                    ·
                      rfl

theorem cell22_1055137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_1055137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055137 prefixEnd_1055137 := by exact prefixLift 1055137
  have htrace : WordTrace (prefixWord ++ tailWord_1055137) baseStart_1055137 baseEnd_1055137 := by
    simpa [prefixWord, tailWord_1055137, baseEnd_1055137] using wordTrace_append hprefix tailTrace_1055137
  have hstable : (prefixWord ++ tailWord_1055137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055137).length < 2 ^ (prefixWord ++ tailWord_1055137).sum := by decide
  have hdescent : baseEnd_1055137 < baseStart_1055137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055156 : List Nat := [2, 5, 2, 2, 1, 1, 2, 2, 2, 3]
def baseStart_1055156 : Nat := 118140960795 + 1055156 * 2 ^ 59
def prefixEnd_1055156 : Nat := 4983230072969 + 3 ^ 40 * 1055156 * 2
def baseEnd_1055156 : Nat := 361201462317052620664955

theorem tailTrace_1055156 : CollatzResearch.WordTrace tailWord_1055156 prefixEnd_1055156 361201462317052620664955 := by
  unfold tailWord_1055156
  simp only [CollatzResearch.WordTrace]
  refine ⟨19242350482678746571476661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25656467310238328761968881 19242350482678746571476661)
  ·
    refine ⟨1803970357751132491075937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 19242350482678746571476661 1803970357751132491075937)
    ·
      refine ⟨1352977768313349368306953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1803970357751132491075937 1352977768313349368306953)
      ·
        refine ⟨1014733326235012026230215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1352977768313349368306953 1014733326235012026230215)
        ·
          refine ⟨1522099989352518039345323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014733326235012026230215 1522099989352518039345323)
          ·
            refine ⟨2283149984028777059017985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522099989352518039345323 2283149984028777059017985)
            ·
              refine ⟨1712362488021582794263489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2283149984028777059017985 1712362488021582794263489)
              ·
                refine ⟨1284271866016187095697617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1712362488021582794263489 1284271866016187095697617)
                ·
                  refine ⟨963203899512140321773213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1284271866016187095697617 963203899512140321773213)
                  ·
                    refine ⟨361201462317052620664955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963203899512140321773213 361201462317052620664955)
                    ·
                      rfl

theorem cell22_1055156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 2, 2, 3].length) (baseStart_1055156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055156 prefixEnd_1055156 := by exact prefixLift 1055156
  have htrace : WordTrace (prefixWord ++ tailWord_1055156) baseStart_1055156 baseEnd_1055156 := by
    simpa [prefixWord, tailWord_1055156, baseEnd_1055156] using wordTrace_append hprefix tailTrace_1055156
  have hstable : (prefixWord ++ tailWord_1055156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055156).length < 2 ^ (prefixWord ++ tailWord_1055156).sum := by decide
  have hdescent : baseEnd_1055156 < baseStart_1055156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055169 : List Nat := [1, 2, 7, 1, 1, 2, 1, 7]
def baseStart_1055169 : Nat := 118140960795 + 1055169 * 2 ^ 59
def prefixEnd_1055169 : Nat := 4983230072969 + 3 ^ 40 * 1055169 * 2
def baseEnd_1055169 : Nat := 40133990275858324454435

theorem tailTrace_1055169 : CollatzResearch.WordTrace tailWord_1055169 prefixEnd_1055169 40133990275858324454435 := by
  unfold tailWord_1055169
  simp only [CollatzResearch.WordTrace]
  refine ⟨38485175114310396363176561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25656783409540264242117707 38485175114310396363176561)
  ·
    refine ⟨28863881335732797272382421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38485175114310396363176561 28863881335732797272382421)
    ·
      refine ⟨676497218806237436071463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 28863881335732797272382421 676497218806237436071463)
      ·
        refine ⟨1014745828209356154107195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676497218806237436071463 1014745828209356154107195)
        ·
          refine ⟨1522118742314034231160793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1014745828209356154107195 1522118742314034231160793)
          ·
            refine ⟨1141589056735525673370595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1522118742314034231160793 1141589056735525673370595)
            ·
              refine ⟨1712383585103288510055893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1141589056735525673370595 1712383585103288510055893)
              ·
                refine ⟨40133990275858324454435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1712383585103288510055893 40133990275858324454435)
                ·
                  rfl

theorem cell22_1055169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 7].length) (baseStart_1055169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055169 prefixEnd_1055169 := by exact prefixLift 1055169
  have htrace : WordTrace (prefixWord ++ tailWord_1055169) baseStart_1055169 baseEnd_1055169 := by
    simpa [prefixWord, tailWord_1055169, baseEnd_1055169] using wordTrace_append hprefix tailTrace_1055169
  have hstable : (prefixWord ++ tailWord_1055169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055169).length < 2 ^ (prefixWord ++ tailWord_1055169).sum := by decide
  have hdescent : baseEnd_1055169 < baseStart_1055169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055178 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 2, 5]
def baseStart_1055178 : Nat := 118140960795 + 1055178 * 2 ^ 59
def prefixEnd_1055178 : Nat := 4983230072969 + 3 ^ 40 * 1055178 * 2
def baseEnd_1055178 : Nat := 361208993366651896614887

theorem tailTrace_1055178 : CollatzResearch.WordTrace tailWord_1055178 prefixEnd_1055178 361208993366651896614887 := by
  unfold tailWord_1055178
  simp only [CollatzResearch.WordTrace]
  refine ⟨9621375842819447725063547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25657002247518527266836125 9621375842819447725063547)
  ·
    refine ⟨14432063764229171587595321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9621375842819447725063547 14432063764229171587595321)
    ·
      refine ⟨10824047823171878690696491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14432063764229171587595321 10824047823171878690696491)
      ·
        refine ⟨16236071734757818036044737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824047823171878690696491 16236071734757818036044737)
        ·
          refine ⟨12177053801068363527033553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16236071734757818036044737 12177053801068363527033553)
          ·
            refine ⟨9132790350801272645275165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12177053801068363527033553 9132790350801272645275165)
            ·
              refine ⟨3424796381550477241978187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9132790350801272645275165 3424796381550477241978187)
              ·
                refine ⟨5137194572325715862967281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3424796381550477241978187 5137194572325715862967281)
                ·
                  refine ⟨3852895929244286897225461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5137194572325715862967281 3852895929244286897225461)
                  ·
                    refine ⟨361208993366651896614887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3852895929244286897225461 361208993366651896614887)
                    ·
                      rfl

theorem cell22_1055178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 2, 5].length) (baseStart_1055178 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055178 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055178 prefixEnd_1055178 := by exact prefixLift 1055178
  have htrace : WordTrace (prefixWord ++ tailWord_1055178) baseStart_1055178 baseEnd_1055178 := by
    simpa [prefixWord, tailWord_1055178, baseEnd_1055178] using wordTrace_append hprefix tailTrace_1055178
  have hstable : (prefixWord ++ tailWord_1055178).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055178).length < 2 ^ (prefixWord ++ tailWord_1055178).sum := by decide
  have hdescent : baseEnd_1055178 < baseStart_1055178 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055193 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 3, 4]
def baseStart_1055193 : Nat := 118140960795 + 1055193 * 2 ^ 59
def prefixEnd_1055193 : Nat := 4983230072969 + 3 ^ 40 * 1055193 * 2
def baseEnd_1055193 : Nat := 361214128173196857489841

theorem tailTrace_1055193 : CollatzResearch.WordTrace tailWord_1055193 prefixEnd_1055193 361214128173196857489841 := by
  unfold tailWord_1055193
  simp only [CollatzResearch.WordTrace]
  refine ⟨38486050466223448462050233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25657366977482298974700155 38486050466223448462050233)
  ·
    refine ⟨28864537849667586346537675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38486050466223448462050233 28864537849667586346537675)
    ·
      refine ⟨43296806774501379519806513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28864537849667586346537675 43296806774501379519806513)
      ·
        refine ⟨32472605080876034639854885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43296806774501379519806513 32472605080876034639854885)
        ·
          refine ⟨6088613452664256494972791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32472605080876034639854885 6088613452664256494972791)
          ·
            refine ⟨9132920178996384742459187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088613452664256494972791 9132920178996384742459187)
            ·
              refine ⟨13699380268494577113688781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9132920178996384742459187 13699380268494577113688781)
              ·
                refine ⟨5137267600685466417633293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13699380268494577113688781 5137267600685466417633293)
                ·
                  refine ⟨1926475350257049906612485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5137267600685466417633293 1926475350257049906612485)
                  ·
                    refine ⟨361214128173196857489841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926475350257049906612485 361214128173196857489841)
                    ·
                      rfl

theorem cell22_1055193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 3, 4].length) (baseStart_1055193 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055193 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055193 prefixEnd_1055193 := by exact prefixLift 1055193
  have htrace : WordTrace (prefixWord ++ tailWord_1055193) baseStart_1055193 baseEnd_1055193 := by
    simpa [prefixWord, tailWord_1055193, baseEnd_1055193] using wordTrace_append hprefix tailTrace_1055193
  have hstable : (prefixWord ++ tailWord_1055193).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055193).length < 2 ^ (prefixWord ++ tailWord_1055193).sum := by decide
  have hdescent : baseEnd_1055193 < baseStart_1055193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055225 : List Nat := [1, 2, 1, 3, 1, 2, 4, 4, 4]
def baseStart_1055225 : Nat := 118140960795 + 1055225 * 2 ^ 59
def prefixEnd_1055225 : Nat := 4983230072969 + 3 ^ 40 * 1055225 * 2
def baseEnd_1055225 : Nat := 120408360809053146896581

theorem tailTrace_1055225 : CollatzResearch.WordTrace tailWord_1055225 prefixEnd_1055225 120408360809053146896581 := by
  unfold tailWord_1055225
  simp only [CollatzResearch.WordTrace]
  refine ⟨38487217602107517927215129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25658145068071678618143419 38487217602107517927215129)
  ·
    refine ⟨28865413201580638445411347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38487217602107517927215129 28865413201580638445411347)
    ·
      refine ⟨43298119802370957668117021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28865413201580638445411347 43298119802370957668117021)
      ·
        refine ⟨16236794925889109125543883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43298119802370957668117021 16236794925889109125543883)
        ·
          refine ⟨24355192388833663688315825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16236794925889109125543883 24355192388833663688315825)
          ·
            refine ⟨18266394291625247766236869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24355192388833663688315825 18266394291625247766236869)
            ·
              refine ⟨3424948929679733956169413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18266394291625247766236869 3424948929679733956169413)
              ·
                refine ⟨642177924314950116781765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3424948929679733956169413 642177924314950116781765)
                ·
                  refine ⟨120408360809053146896581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642177924314950116781765 120408360809053146896581)
                  ·
                    rfl

theorem cell22_1055225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 4, 4].length) (baseStart_1055225 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055225 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055225 prefixEnd_1055225 := by exact prefixLift 1055225
  have htrace : WordTrace (prefixWord ++ tailWord_1055225) baseStart_1055225 baseEnd_1055225 := by
    simpa [prefixWord, tailWord_1055225, baseEnd_1055225] using wordTrace_append hprefix tailTrace_1055225
  have hstable : (prefixWord ++ tailWord_1055225).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055225).length < 2 ^ (prefixWord ++ tailWord_1055225).sum := by decide
  have hdescent : baseEnd_1055225 < baseStart_1055225 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055253 : List Nat := [1, 3, 2, 1, 3, 1, 3, 8]
def baseStart_1055253 : Nat := 118140960795 + 1055253 * 2 ^ 59
def prefixEnd_1055253 : Nat := 4983230072969 + 3 ^ 40 * 1055253 * 2
def baseEnd_1055253 : Nat := 40137185266597411221073

theorem tailTrace_1055253 : CollatzResearch.WordTrace tailWord_1055253 prefixEnd_1055253 40137185266597411221073 := by
  unfold tailWord_1055253
  simp only [CollatzResearch.WordTrace]
  refine ⟨38488238846006078709234413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25658825897337385806156275 38488238846006078709234413)
  ·
    refine ⟨14433089567252279515962905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38488238846006078709234413 14433089567252279515962905)
    ·
      refine ⟨10824817175439209636972179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14433089567252279515962905 10824817175439209636972179)
      ·
        refine ⟨16237225763158814455458269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10824817175439209636972179 16237225763158814455458269)
        ·
          refine ⟨6088959661184555420796851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16237225763158814455458269 6088959661184555420796851)
          ·
            refine ⟨9133439491776833131195277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6088959661184555420796851 9133439491776833131195277)
            ·
              refine ⟨3425039809416312424198229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9133439491776833131195277 3425039809416312424198229)
              ·
                refine ⟨40137185266597411221073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3425039809416312424198229 40137185266597411221073)
                ·
                  rfl

theorem cell22_1055253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 8].length) (baseStart_1055253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055253 prefixEnd_1055253 := by exact prefixLift 1055253
  have htrace : WordTrace (prefixWord ++ tailWord_1055253) baseStart_1055253 baseEnd_1055253 := by
    simpa [prefixWord, tailWord_1055253, baseEnd_1055253] using wordTrace_append hprefix tailTrace_1055253
  have hstable : (prefixWord ++ tailWord_1055253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055253).length < 2 ^ (prefixWord ++ tailWord_1055253).sum := by decide
  have hdescent : baseEnd_1055253 < baseStart_1055253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055272 : List Nat := [2, 1, 5, 2, 1, 2, 1, 2, 2, 4]
def baseStart_1055272 : Nat := 118140960795 + 1055272 * 2 ^ 59
def prefixEnd_1055272 : Nat := 4983230072969 + 3 ^ 40 * 1055272 * 2
def baseEnd_1055272 : Nat := 361241171487666984764599

theorem tailTrace_1055272 : CollatzResearch.WordTrace tailWord_1055272 prefixEnd_1055272 361241171487666984764599 := by
  unfold tailWord_1055272
  simp only [CollatzResearch.WordTrace]
  refine ⟨19244465916468622477088035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25659287888624829969450713 19244465916468622477088035)
  ·
    refine ⟨28866698874702933715632053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19244465916468622477088035 28866698874702933715632053)
    ·
      refine ⟨2706253019503400035840505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28866698874702933715632053 2706253019503400035840505)
      ·
        refine ⟨2029689764627550026880379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2706253019503400035840505 2029689764627550026880379)
        ·
          refine ⟨3044534646941325040320569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2029689764627550026880379 3044534646941325040320569)
          ·
            refine ⟨2283400985205993780240427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3044534646941325040320569 2283400985205993780240427)
            ·
              refine ⟨3425101477808990670360641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283400985205993780240427 3425101477808990670360641)
              ·
                refine ⟨2568826108356743002770481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425101477808990670360641 2568826108356743002770481)
                ·
                  refine ⟨1926619581267557252077861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2568826108356743002770481 1926619581267557252077861)
                  ·
                    refine ⟨361241171487666984764599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1926619581267557252077861 361241171487666984764599)
                    ·
                      rfl

theorem cell22_1055272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_1055272 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055272 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055272 prefixEnd_1055272 := by exact prefixLift 1055272
  have htrace : WordTrace (prefixWord ++ tailWord_1055272) baseStart_1055272 baseEnd_1055272 := by
    simpa [prefixWord, tailWord_1055272, baseEnd_1055272] using wordTrace_append hprefix tailTrace_1055272
  have hstable : (prefixWord ++ tailWord_1055272).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055272).length < 2 ^ (prefixWord ++ tailWord_1055272).sum := by decide
  have hdescent : baseEnd_1055272 < baseStart_1055272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055283 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 2, 6]
def baseStart_1055283 : Nat := 118140960795 + 1055283 * 2 ^ 59
def prefixEnd_1055283 : Nat := 4983230072969 + 3 ^ 40 * 1055283 * 2
def baseEnd_1055283 : Nat := 361244937012466622739565

theorem tailTrace_1055283 : CollatzResearch.WordTrace tailWord_1055283 prefixEnd_1055283 361244937012466622739565 := by
  unfold tailWord_1055283
  simp only [CollatzResearch.WordTrace]
  refine ⟨38489333035897393832826503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25659555357264929221884335 38489333035897393832826503)
  ·
    refine ⟨57733999553846090749239755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38489333035897393832826503 57733999553846090749239755)
    ·
      refine ⟨86600999330769136123859633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57733999553846090749239755 86600999330769136123859633)
      ·
        refine ⟨64950749498076852092894725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86600999330769136123859633 64950749498076852092894725)
        ·
          refine ⟨12178265530889409767417761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64950749498076852092894725 12178265530889409767417761)
          ·
            refine ⟨9133699148167057325563321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12178265530889409767417761 9133699148167057325563321)
            ·
              refine ⟨6850274361125292994172491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9133699148167057325563321 6850274361125292994172491)
              ·
                refine ⟨10275411541687939491258737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6850274361125292994172491 10275411541687939491258737)
                ·
                  refine ⟨7706558656265954618444053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10275411541687939491258737 7706558656265954618444053)
                  ·
                    refine ⟨361244937012466622739565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 7706558656265954618444053 361244937012466622739565)
                    ·
                      rfl

theorem cell22_1055283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 2, 6].length) (baseStart_1055283 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055283 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055283 prefixEnd_1055283 := by exact prefixLift 1055283
  have htrace : WordTrace (prefixWord ++ tailWord_1055283) baseStart_1055283 baseEnd_1055283 := by
    simpa [prefixWord, tailWord_1055283, baseEnd_1055283] using wordTrace_append hprefix tailTrace_1055283
  have hstable : (prefixWord ++ tailWord_1055283).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055283).length < 2 ^ (prefixWord ++ tailWord_1055283).sum := by decide
  have hdescent : baseEnd_1055283 < baseStart_1055283 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055336 : List Nat := [2, 1, 4, 3, 2, 1, 1, 4, 1, 3]
def baseStart_1055336 : Nat := 118140960795 + 1055336 * 2 ^ 59
def prefixEnd_1055336 : Nat := 4983230072969 + 3 ^ 40 * 1055336 * 2
def baseEnd_1055336 : Nat := 361263079995592151164403

theorem tailTrace_1055336 : CollatzResearch.WordTrace tailWord_1055336 prefixEnd_1055336 361263079995592151164403 := by
  unfold tailWord_1055336
  simp only [CollatzResearch.WordTrace]
  refine ⟨19245633052352691942252931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25660844069803589256337241 19245633052352691942252931)
  ·
    refine ⟨28868449578529037913379397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19245633052352691942252931 28868449578529037913379397)
    ·
      refine ⟨5412834295974194608758637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28868449578529037913379397 5412834295974194608758637)
      ·
        refine ⟨2029812860990322978284489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5412834295974194608758637 2029812860990322978284489)
        ·
          refine ⟨1522359645742742233713367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2029812860990322978284489 1522359645742742233713367)
          ·
            refine ⟨2283539468614113350570051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522359645742742233713367 2283539468614113350570051)
            ·
              refine ⟨3425309202921170025855077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283539468614113350570051 3425309202921170025855077)
              ·
                refine ⟨642245475547719379847827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3425309202921170025855077 642245475547719379847827)
                ·
                  refine ⟨963368213321579069771741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642245475547719379847827 963368213321579069771741)
                  ·
                    refine ⟨361263079995592151164403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963368213321579069771741 361263079995592151164403)
                    ·
                      rfl

theorem cell22_1055336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_1055336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055336 prefixEnd_1055336 := by exact prefixLift 1055336
  have htrace : WordTrace (prefixWord ++ tailWord_1055336) baseStart_1055336 baseEnd_1055336 := by
    simpa [prefixWord, tailWord_1055336, baseEnd_1055336] using wordTrace_append hprefix tailTrace_1055336
  have hstable : (prefixWord ++ tailWord_1055336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055336).length < 2 ^ (prefixWord ++ tailWord_1055336).sum := by decide
  have hdescent : baseEnd_1055336 < baseStart_1055336 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055360 : List Nat := [2, 1, 1, 2, 1, 6, 1, 2, 6]
def baseStart_1055360 : Nat := 118140960795 + 1055360 * 2 ^ 59
def prefixEnd_1055360 : Nat := 4983230072969 + 3 ^ 40 * 1055360 * 2
def baseEnd_1055360 : Nat := 120423765228688029521443

theorem tailTrace_1055360 : CollatzResearch.WordTrace tailWord_1055360 prefixEnd_1055360 120423765228688029521443 := by
  unfold tailWord_1055360
  simp only [CollatzResearch.WordTrace]
  refine ⟨19246070728309217991689767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25661427637745623988919689 19246070728309217991689767)
  ·
    refine ⟨28869106092463826987534651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19246070728309217991689767 28869106092463826987534651)
    ·
      refine ⟨43303659138695740481301977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28869106092463826987534651 43303659138695740481301977)
      ·
        refine ⟨32477744354021805360976483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43303659138695740481301977 32477744354021805360976483)
        ·
          refine ⟨48716616531032708041464725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32477744354021805360976483 48716616531032708041464725)
          ·
            refine ⟨2283591399892158189443659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 48716616531032708041464725 2283591399892158189443659)
            ·
              refine ⟨3425387099838237284165489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2283591399892158189443659 3425387099838237284165489)
              ·
                refine ⟨2569040324878677963124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3425387099838237284165489 2569040324878677963124117)
                ·
                  refine ⟨120423765228688029521443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2569040324878677963124117 120423765228688029521443)
                  ·
                    rfl

theorem cell22_1055360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 2, 6].length) (baseStart_1055360 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055360 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055360 prefixEnd_1055360 := by exact prefixLift 1055360
  have htrace : WordTrace (prefixWord ++ tailWord_1055360) baseStart_1055360 baseEnd_1055360 := by
    simpa [prefixWord, tailWord_1055360, baseEnd_1055360] using wordTrace_append hprefix tailTrace_1055360
  have hstable : (prefixWord ++ tailWord_1055360).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055360).length < 2 ^ (prefixWord ++ tailWord_1055360).sum := by decide
  have hdescent : baseEnd_1055360 < baseStart_1055360 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055375 : List Nat := [1, 1, 2, 1, 1, 1, 1, 5, 6, 3]
def baseStart_1055375 : Nat := 118140960795 + 1055375 * 2 ^ 59
def prefixEnd_1055375 : Nat := 4983230072969 + 3 ^ 40 * 1055375 * 2
def baseEnd_1055375 : Nat := 361276430492609049439283

theorem tailTrace_1055375 : CollatzResearch.WordTrace tailWord_1055375 prefixEnd_1055375 361276430492609049439283 := by
  unfold tailWord_1055375
  simp only [CollatzResearch.WordTrace]
  refine ⟨38492688551564093545175579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25661792367709395696783719 38492688551564093545175579)
  ·
    refine ⟨57739032827346140317763369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38492688551564093545175579 57739032827346140317763369)
    ·
      refine ⟨43304274620509605238322527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57739032827346140317763369 43304274620509605238322527)
      ·
        refine ⟨64956411930764407857483791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43304274620509605238322527 64956411930764407857483791)
        ·
          refine ⟨97434617896146611786225687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64956411930764407857483791 97434617896146611786225687)
          ·
            refine ⟨146151926844219917679338531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 97434617896146611786225687 146151926844219917679338531)
            ·
              refine ⟨219227890266329876519007797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 146151926844219917679338531 219227890266329876519007797)
              ·
                refine ⟨20552614712468425923656981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 219227890266329876519007797 20552614712468425923656981)
                ·
                  refine ⟨963403814646957465171421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 20552614712468425923656981 963403814646957465171421)
                  ·
                    refine ⟨361276430492609049439283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963403814646957465171421 361276430492609049439283)
                    ·
                      rfl

theorem cell22_1055375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 5, 6, 3].length) (baseStart_1055375 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055375 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055375 prefixEnd_1055375 := by exact prefixLift 1055375
  have htrace : WordTrace (prefixWord ++ tailWord_1055375) baseStart_1055375 baseEnd_1055375 := by
    simpa [prefixWord, tailWord_1055375, baseEnd_1055375] using wordTrace_append hprefix tailTrace_1055375
  have hstable : (prefixWord ++ tailWord_1055375).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055375).length < 2 ^ (prefixWord ++ tailWord_1055375).sum := by decide
  have hdescent : baseEnd_1055375 < baseStart_1055375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055420 : List Nat := [2, 2, 2, 3, 1, 1, 1, 1, 2, 7]
def baseStart_1055420 : Nat := 118140960795 + 1055420 * 2 ^ 59
def prefixEnd_1055420 : Nat := 4983230072969 + 3 ^ 40 * 1055420 * 2
def baseEnd_1055420 : Nat := 361291834912243932064145

theorem tailTrace_1055420 : CollatzResearch.WordTrace tailWord_1055420 prefixEnd_1055420 361291834912243932064145 := by
  unfold tailWord_1055420
  simp only [CollatzResearch.WordTrace]
  refine ⟨19247164918200533115281857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25662886557600710820375809 19247164918200533115281857)
  ·
    refine ⟨14435373688650399836461393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19247164918200533115281857 14435373688650399836461393)
    ·
      refine ⟨10826530266487799877346045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14435373688650399836461393 10826530266487799877346045)
      ·
        refine ⟨4059948849932924954004767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10826530266487799877346045 4059948849932924954004767)
        ·
          refine ⟨6089923274899387431007151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4059948849932924954004767 6089923274899387431007151)
          ·
            refine ⟨9134884912349081146510727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6089923274899387431007151 9134884912349081146510727)
            ·
              refine ⟨13702327368523621719766091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9134884912349081146510727 13702327368523621719766091)
              ·
                refine ⟨20553491052785432579649137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13702327368523621719766091 20553491052785432579649137)
                ·
                  refine ⟨15415118289589074434736853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20553491052785432579649137 15415118289589074434736853)
                  ·
                    refine ⟨361291834912243932064145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15415118289589074434736853 361291834912243932064145)
                    ·
                      rfl

theorem cell22_1055420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 1, 2, 7].length) (baseStart_1055420 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055420 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055420 prefixEnd_1055420 := by exact prefixLift 1055420
  have htrace : WordTrace (prefixWord ++ tailWord_1055420) baseStart_1055420 baseEnd_1055420 := by
    simpa [prefixWord, tailWord_1055420, baseEnd_1055420] using wordTrace_append hprefix tailTrace_1055420
  have hstable : (prefixWord ++ tailWord_1055420).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055420).length < 2 ^ (prefixWord ++ tailWord_1055420).sum := by decide
  have hdescent : baseEnd_1055420 < baseStart_1055420 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055450 : List Nat := [3, 1, 1, 2, 2, 2, 1, 3, 7]
def baseStart_1055450 : Nat := 118140960795 + 1055450 * 2 ^ 59
def prefixEnd_1055450 : Nat := 4983230072969 + 3 ^ 40 * 1055450 * 2
def baseEnd_1055450 : Nat := 120434034841777951271351

theorem tailTrace_1055450 : CollatzResearch.WordTrace tailWord_1055450 prefixEnd_1055450 120434034841777951271351 := by
  unfold tailWord_1055450
  simp only [CollatzResearch.WordTrace]
  refine ⟨9623856006573095338538951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25663616017528254236103869 9623856006573095338538951)
  ·
    refine ⟨14435784009859643007808427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9623856006573095338538951 14435784009859643007808427)
    ·
      refine ⟨21653676014789464511712641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14435784009859643007808427 21653676014789464511712641)
      ·
        refine ⟨16240257011092098383784481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21653676014789464511712641 16240257011092098383784481)
        ·
          refine ⟨12180192758319073787838361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16240257011092098383784481 12180192758319073787838361)
          ·
            refine ⟨9135144568739305340878771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12180192758319073787838361 9135144568739305340878771)
            ·
              refine ⟨13702716853108958011318157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9135144568739305340878771 13702716853108958011318157)
              ·
                refine ⟨5138518819915859254244309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13702716853108958011318157 5138518819915859254244309)
                ·
                  refine ⟨120434034841777951271351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5138518819915859254244309 120434034841777951271351)
                  ·
                    rfl

theorem cell22_1055450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 3, 7].length) (baseStart_1055450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055450 prefixEnd_1055450 := by exact prefixLift 1055450
  have htrace : WordTrace (prefixWord ++ tailWord_1055450) baseStart_1055450 baseEnd_1055450 := by
    simpa [prefixWord, tailWord_1055450, baseEnd_1055450] using wordTrace_append hprefix tailTrace_1055450
  have hstable : (prefixWord ++ tailWord_1055450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055450).length < 2 ^ (prefixWord ++ tailWord_1055450).sum := by decide
  have hdescent : baseEnd_1055450 < baseStart_1055450 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055465 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 2, 5]
def baseStart_1055465 : Nat := 118140960795 + 1055465 * 2 ^ 59
def prefixEnd_1055465 : Nat := 4983230072969 + 3 ^ 40 * 1055465 * 2
def baseEnd_1055465 : Nat := 361307239331878814689007

theorem tailTrace_1055465 : CollatzResearch.WordTrace tailWord_1055465 prefixEnd_1055465 361307239331878814689007 := by
  unfold tailWord_1055465
  simp only [CollatzResearch.WordTrace]
  refine ⟨38495971121238038915951849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25663980747492025943967899 38495971121238038915951849)
  ·
    refine ⟨28871978340928529186963887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38495971121238038915951849 28871978340928529186963887)
    ·
      refine ⟨43307967511392793780445831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28871978340928529186963887 43307967511392793780445831)
      ·
        refine ⟨64961951267089190670668747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43307967511392793780445831 64961951267089190670668747)
        ·
          refine ⟨97442926900633786006003121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64961951267089190670668747 97442926900633786006003121)
          ·
            refine ⟨73082195175475339504502341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97442926900633786006003121 73082195175475339504502341)
            ·
              refine ⟨13702911595401626157094189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 73082195175475339504502341 13702911595401626157094189)
              ·
                refine ⟨5138591848275609808910321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13702911595401626157094189 5138591848275609808910321)
                ·
                  refine ⟨3853943886206707356682741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5138591848275609808910321 3853943886206707356682741)
                  ·
                    refine ⟨361307239331878814689007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3853943886206707356682741 361307239331878814689007)
                    ·
                      rfl

theorem cell22_1055465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 2, 5].length) (baseStart_1055465 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055465 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055465 prefixEnd_1055465 := by exact prefixLift 1055465
  have htrace : WordTrace (prefixWord ++ tailWord_1055465) baseStart_1055465 baseEnd_1055465 := by
    simpa [prefixWord, tailWord_1055465, baseEnd_1055465] using wordTrace_append hprefix tailTrace_1055465
  have hstable : (prefixWord ++ tailWord_1055465).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055465).length < 2 ^ (prefixWord ++ tailWord_1055465).sum := by decide
  have hdescent : baseEnd_1055465 < baseStart_1055465 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055497 : List Nat := [1, 2, 1, 1, 3, 2, 2, 5, 1, 4]
def baseStart_1055497 : Nat := 118140960795 + 1055497 * 2 ^ 59
def prefixEnd_1055497 : Nat := 4983230072969 + 3 ^ 40 * 1055497 * 2
def baseEnd_1055497 : Nat := 361318193585841397888909

theorem tailTrace_1055497 : CollatzResearch.WordTrace tailWord_1055497 prefixEnd_1055497 361318193585841397888909 := by
  unfold tailWord_1055497
  simp only [CollatzResearch.WordTrace]
  refine ⟨38497138257122108381116745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25664758838081405587411163 38497138257122108381116745)
  ·
    refine ⟨28872853692841581285837559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38497138257122108381116745 28872853692841581285837559)
    ·
      refine ⟨43309280539262371928756339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28872853692841581285837559 43309280539262371928756339)
      ·
        refine ⟨64963920808893557893134509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43309280539262371928756339 64963920808893557893134509)
        ·
          refine ⟨24361470303335084209925441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64963920808893557893134509 24361470303335084209925441)
          ·
            refine ⟨18271102727501313157444081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24361470303335084209925441 18271102727501313157444081)
            ·
              refine ⟨13703327045625984868083061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18271102727501313157444081 13703327045625984868083061)
              ·
                refine ⟨1284686910527436081382787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 13703327045625984868083061 1284686910527436081382787)
                ·
                  refine ⟨1927030365791154122074181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284686910527436081382787 1927030365791154122074181)
                  ·
                    refine ⟨361318193585841397888909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927030365791154122074181 361318193585841397888909)
                    ·
                      rfl

theorem cell22_1055497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 5, 1, 4].length) (baseStart_1055497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055497 prefixEnd_1055497 := by exact prefixLift 1055497
  have htrace : WordTrace (prefixWord ++ tailWord_1055497) baseStart_1055497 baseEnd_1055497 := by
    simpa [prefixWord, tailWord_1055497, baseEnd_1055497] using wordTrace_append hprefix tailTrace_1055497
  have hstable : (prefixWord ++ tailWord_1055497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055497).length < 2 ^ (prefixWord ++ tailWord_1055497).sum := by decide
  have hdescent : baseEnd_1055497 < baseStart_1055497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055546 : List Nat := [3, 1, 1, 1, 6, 1, 2, 3, 4]
def baseStart_1055546 : Nat := 118140960795 + 1055546 * 2 ^ 59
def prefixEnd_1055546 : Nat := 4983230072969 + 3 ^ 40 * 1055546 * 2
def baseEnd_1055546 : Nat := 120444989095740534471253

theorem tailTrace_1055546 : CollatzResearch.WordTrace tailWord_1055546 prefixEnd_1055546 120444989095740534471253 := by
  unfold tailWord_1055546
  simp only [CollatzResearch.WordTrace]
  refine ⟨9624731358486147437412623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25665950289296393166433661 9624731358486147437412623)
  ·
    refine ⟨14437097037729221156118935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9624731358486147437412623 14437097037729221156118935)
    ·
      refine ⟨21655645556593831734178403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14437097037729221156118935 21655645556593831734178403)
      ·
        refine ⟨32483468334890747601267605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21655645556593831734178403 32483468334890747601267605)
        ·
          refine ⟨1522662578198003793809419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 32483468334890747601267605 1522662578198003793809419)
          ·
            refine ⟨2283993867297005690714129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522662578198003793809419 2283993867297005690714129)
            ·
              refine ⟨1712995400472754268035597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2283993867297005690714129 1712995400472754268035597)
              ·
                refine ⟨642373275177282850513349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1712995400472754268035597 642373275177282850513349)
                ·
                  refine ⟨120444989095740534471253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642373275177282850513349 120444989095740534471253)
                  ·
                    rfl

theorem cell22_1055546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 3, 4].length) (baseStart_1055546 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055546 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055546 prefixEnd_1055546 := by exact prefixLift 1055546
  have htrace : WordTrace (prefixWord ++ tailWord_1055546) baseStart_1055546 baseEnd_1055546 := by
    simpa [prefixWord, tailWord_1055546, baseEnd_1055546] using wordTrace_append hprefix tailTrace_1055546
  have hstable : (prefixWord ++ tailWord_1055546).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055546).length < 2 ^ (prefixWord ++ tailWord_1055546).sum := by decide
  have hdescent : baseEnd_1055546 < baseStart_1055546 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055561 : List Nat := [1, 2, 1, 1, 2, 7, 1, 2, 2, 3]
def baseStart_1055561 : Nat := 118140960795 + 1055561 * 2 ^ 59
def prefixEnd_1055561 : Nat := 4983230072969 + 3 ^ 40 * 1055561 * 2
def baseEnd_1055561 : Nat := 361340102093766564288713

theorem tailTrace_1055561 : CollatzResearch.WordTrace tailWord_1055561 prefixEnd_1055561 361340102093766564288713 := by
  unfold tailWord_1055561
  simp only [CollatzResearch.WordTrace]
  refine ⟨38499472528890247311446537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25666315019260164874297691 38499472528890247311446537)
  ·
    refine ⟨28874604396667685483584903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38499472528890247311446537 28874604396667685483584903)
    ·
      refine ⟨43311906595001528225377355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28874604396667685483584903 43311906595001528225377355)
      ·
        refine ⟨64967859892502292338066033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43311906595001528225377355 64967859892502292338066033)
        ·
          refine ⟨48725894919376719253549525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64967859892502292338066033 48725894919376719253549525)
          ·
            refine ⟨1142013162172891857505067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 48725894919376719253549525 1142013162172891857505067)
            ·
              refine ⟨1713019743259337786257601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142013162172891857505067 1713019743259337786257601)
              ·
                refine ⟨1284764807444503339693201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713019743259337786257601 1284764807444503339693201)
                ·
                  refine ⟨963573605583377504769901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1284764807444503339693201 963573605583377504769901)
                  ·
                    refine ⟨361340102093766564288713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963573605583377504769901 361340102093766564288713)
                    ·
                      rfl

theorem cell22_1055561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 2, 2, 3].length) (baseStart_1055561 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055561 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055561 prefixEnd_1055561 := by exact prefixLift 1055561
  have htrace : WordTrace (prefixWord ++ tailWord_1055561) baseStart_1055561 baseEnd_1055561 := by
    simpa [prefixWord, tailWord_1055561, baseEnd_1055561] using wordTrace_append hprefix tailTrace_1055561
  have hstable : (prefixWord ++ tailWord_1055561).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055561).length < 2 ^ (prefixWord ++ tailWord_1055561).sum := by decide
  have hdescent : baseEnd_1055561 < baseStart_1055561 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055589 : List Nat := [1, 3, 1, 3, 1, 1, 4, 2, 3, 3]
def baseStart_1055589 : Nat := 118140960795 + 1055589 * 2 ^ 59
def prefixEnd_1055589 : Nat := 4983230072969 + 3 ^ 40 * 1055589 * 2
def baseEnd_1055589 : Nat := 361349687065983824588627

theorem tailTrace_1055589 : CollatzResearch.WordTrace tailWord_1055589 prefixEnd_1055589 361349687065983824588627 := by
  unfold tailWord_1055589
  simp only [CollatzResearch.WordTrace]
  refine ⟨38500493772788808093465821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25666995848525872062310547 38500493772788808093465821)
  ·
    refine ⟨14437685164795803035049683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38500493772788808093465821 14437685164795803035049683)
    ·
      refine ⟨21656527747193704552574525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14437685164795803035049683 21656527747193704552574525)
      ·
        refine ⟨8121197905197639207215447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21656527747193704552574525 8121197905197639207215447)
        ·
          refine ⟨12181796857796458810823171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8121197905197639207215447 12181796857796458810823171)
          ·
            refine ⟨18272695286694688216234757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12181796857796458810823171 18272695286694688216234757)
            ·
              refine ⟨3426130366255254040544017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18272695286694688216234757 3426130366255254040544017)
              ·
                refine ⟨2569597774691440530408013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3426130366255254040544017 2569597774691440530408013)
                ·
                  refine ⟨963599165509290198903005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2569597774691440530408013 963599165509290198903005)
                  ·
                    refine ⟨361349687065983824588627, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963599165509290198903005 361349687065983824588627)
                    ·
                      rfl

theorem cell22_1055589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 2, 3, 3].length) (baseStart_1055589 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055589 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055589 prefixEnd_1055589 := by exact prefixLift 1055589
  have htrace : WordTrace (prefixWord ++ tailWord_1055589) baseStart_1055589 baseEnd_1055589 := by
    simpa [prefixWord, tailWord_1055589, baseEnd_1055589] using wordTrace_append hprefix tailTrace_1055589
  have hstable : (prefixWord ++ tailWord_1055589).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055589).length < 2 ^ (prefixWord ++ tailWord_1055589).sum := by decide
  have hdescent : baseEnd_1055589 < baseStart_1055589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055602 : List Nat := [3, 2, 1, 2, 1, 1, 3, 2, 7]
def baseStart_1055602 : Nat := 118140960795 + 1055602 * 2 ^ 59
def prefixEnd_1055602 : Nat := 4983230072969 + 3 ^ 40 * 1055602 * 2
def baseEnd_1055602 : Nat := 120451379077218708004529

theorem tailTrace_1055602 : CollatzResearch.WordTrace tailWord_1055602 prefixEnd_1055602 120451379077218708004529 := by
  unfold tailWord_1055602
  simp only [CollatzResearch.WordTrace]
  refine ⟨9625241980435427828422265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25667311947827807542459373 9625241980435427828422265)
  ·
    refine ⟨7218931485326570871316699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9625241980435427828422265 7218931485326570871316699)
    ·
      refine ⟨10828397227989856306975049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7218931485326570871316699 10828397227989856306975049)
      ·
        refine ⟨8121297920992392230231287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10828397227989856306975049 8121297920992392230231287)
        ·
          refine ⟨12181946881488588345346931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8121297920992392230231287 12181946881488588345346931)
          ·
            refine ⟨18272920322232882518020397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12181946881488588345346931 18272920322232882518020397)
            ·
              refine ⟨6852345120837330944257649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18272920322232882518020397 6852345120837330944257649)
              ·
                refine ⟨5139258840627998208193237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6852345120837330944257649 5139258840627998208193237)
                ·
                  refine ⟨120451379077218708004529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5139258840627998208193237 120451379077218708004529)
                  ·
                    rfl

theorem cell22_1055602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 2, 7].length) (baseStart_1055602 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055602 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055602 prefixEnd_1055602 := by exact prefixLift 1055602
  have htrace : WordTrace (prefixWord ++ tailWord_1055602) baseStart_1055602 baseEnd_1055602 := by
    simpa [prefixWord, tailWord_1055602, baseEnd_1055602] using wordTrace_append hprefix tailTrace_1055602
  have hstable : (prefixWord ++ tailWord_1055602).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055602).length < 2 ^ (prefixWord ++ tailWord_1055602).sum := by decide
  have hdescent : baseEnd_1055602 < baseStart_1055602 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055717 : List Nat := [1, 3, 1, 6, 2, 1, 2, 1, 1, 4]
def baseStart_1055717 : Nat := 118140960795 + 1055717 * 2 ^ 59
def prefixEnd_1055717 : Nat := 4983230072969 + 3 ^ 40 * 1055717 * 2
def baseEnd_1055717 : Nat := 361393504081834157388235

theorem tailTrace_1055717 : CollatzResearch.WordTrace tailWord_1055717 prefixEnd_1055717 361393504081834157388235 := by
  unfold tailWord_1055717
  simp only [CollatzResearch.WordTrace]
  refine ⟨38505162316325085954125405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25670108210883390636083603 38505162316325085954125405)
  ·
    refine ⟨14439435868621907232797027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38505162316325085954125405 14439435868621907232797027)
    ·
      refine ⟨21659153802932860849195541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14439435868621907232797027 21659153802932860849195541)
      ·
        refine ⟨1015272834512477852306041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 21659153802932860849195541 1015272834512477852306041)
        ·
          refine ⟨761454625884358389229531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015272834512477852306041 761454625884358389229531)
          ·
            refine ⟨1142181938826537583844297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761454625884358389229531 1142181938826537583844297)
            ·
              refine ⟨856636454119903187883223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1142181938826537583844297 856636454119903187883223)
              ·
                refine ⟨1284954681179854781824835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 856636454119903187883223 1284954681179854781824835)
                ·
                  refine ⟨1927432021769782172737253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1284954681179854781824835 1927432021769782172737253)
                  ·
                    refine ⟨361393504081834157388235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927432021769782172737253 361393504081834157388235)
                    ·
                      rfl

theorem cell22_1055717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 1, 1, 4].length) (baseStart_1055717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055717 prefixEnd_1055717 := by exact prefixLift 1055717
  have htrace : WordTrace (prefixWord ++ tailWord_1055717) baseStart_1055717 baseEnd_1055717 := by
    simpa [prefixWord, tailWord_1055717, baseEnd_1055717] using wordTrace_append hprefix tailTrace_1055717
  have hstable : (prefixWord ++ tailWord_1055717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055717).length < 2 ^ (prefixWord ++ tailWord_1055717).sum := by decide
  have hdescent : baseEnd_1055717 < baseStart_1055717 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055732 : List Nat := [2, 6, 2, 1, 1, 1, 2, 1, 6]
def baseStart_1055732 : Nat := 118140960795 + 1055732 * 2 ^ 59
def prefixEnd_1055732 : Nat := 4983230072969 + 3 ^ 40 * 1055732 * 2
def baseEnd_1055732 : Nat := 120466212962793039421063

theorem tailTrace_1055732 : CollatzResearch.WordTrace tailWord_1055732 prefixEnd_1055732 120466212962793039421063 := by
  unfold tailWord_1055732
  simp only [CollatzResearch.WordTrace]
  refine ⟨19252854705635371757960725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25670472940847162343947633 19252854705635371757960725)
  ·
    refine ⟨902477564326658051154409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 19252854705635371757960725 902477564326658051154409)
    ·
      refine ⟨676858173244993538365807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 902477564326658051154409 676858173244993538365807)
      ·
        refine ⟨1015287259867490307548711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 676858173244993538365807 1015287259867490307548711)
        ·
          refine ⟨1522930889801235461323067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1015287259867490307548711 1522930889801235461323067)
          ·
            refine ⟨2284396334701853191984601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1522930889801235461323067 2284396334701853191984601)
            ·
              refine ⟨1713297251026389893988451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2284396334701853191984601 1713297251026389893988451)
              ·
                refine ⟨2569945876539584840982677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713297251026389893988451 2569945876539584840982677)
                ·
                  refine ⟨120466212962793039421063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2569945876539584840982677 120466212962793039421063)
                  ·
                    rfl

theorem cell22_1055732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 1, 6].length) (baseStart_1055732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055732 prefixEnd_1055732 := by exact prefixLift 1055732
  have htrace : WordTrace (prefixWord ++ tailWord_1055732) baseStart_1055732 baseEnd_1055732 := by
    simpa [prefixWord, tailWord_1055732, baseEnd_1055732] using wordTrace_append hprefix tailTrace_1055732
  have hstable : (prefixWord ++ tailWord_1055732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055732).length < 2 ^ (prefixWord ++ tailWord_1055732).sum := by decide
  have hdescent : baseEnd_1055732 < baseStart_1055732 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055775 : List Nat := [1, 1, 2, 4, 1, 5, 1, 3, 1, 3]
def baseStart_1055775 : Nat := 118140960795 + 1055775 * 2 ^ 59
def prefixEnd_1055775 : Nat := 4983230072969 + 3 ^ 40 * 1055775 * 2
def baseEnd_1055775 : Nat := 361413358667141339438057

theorem tailTrace_1055775 : CollatzResearch.WordTrace tailWord_1055775 prefixEnd_1055775 361413358667141339438057 := by
  unfold tailWord_1055775
  simp only [CollatzResearch.WordTrace]
  refine ⟨38507277750114961859736779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25671518500076641239824519 38507277750114961859736779)
  ·
    refine ⟨57760916625172442789605169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38507277750114961859736779 57760916625172442789605169)
    ·
      refine ⟨43320687468879332092203877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57760916625172442789605169 43320687468879332092203877)
      ·
        refine ⟨8122628900414874767288227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43320687468879332092203877 8122628900414874767288227)
        ·
          refine ⟨12183943350622312150932341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8122628900414874767288227 12183943350622312150932341)
          ·
            refine ⟨1142244689120841764149907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 12183943350622312150932341 1142244689120841764149907)
            ·
              refine ⟨1713367033681262646224861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142244689120841764149907 1713367033681262646224861)
              ·
                refine ⟨642512637630473492334323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1713367033681262646224861 642512637630473492334323)
                ·
                  refine ⟨963768956445710238501485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 642512637630473492334323 963768956445710238501485)
                  ·
                    refine ⟨361413358667141339438057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 963768956445710238501485 361413358667141339438057)
                    ·
                      rfl

theorem cell22_1055775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 5, 1, 3, 1, 3].length) (baseStart_1055775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055775 prefixEnd_1055775 := by exact prefixLift 1055775
  have htrace : WordTrace (prefixWord ++ tailWord_1055775) baseStart_1055775 baseEnd_1055775 := by
    simpa [prefixWord, tailWord_1055775, baseEnd_1055775] using wordTrace_append hprefix tailTrace_1055775
  have hstable : (prefixWord ++ tailWord_1055775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055775).length < 2 ^ (prefixWord ++ tailWord_1055775).sum := by decide
  have hdescent : baseEnd_1055775 < baseStart_1055775 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055850 : List Nat := [3, 1, 3, 2, 2, 1, 4, 2, 4]
def baseStart_1055850 : Nat := 118140960795 + 1055850 * 2 ^ 59
def prefixEnd_1055850 : Nat := 4983230072969 + 3 ^ 40 * 1055850 * 2
def baseEnd_1055850 : Nat := 120479677566622047937609

theorem tailTrace_1055850 : CollatzResearch.WordTrace tailWord_1055850 prefixEnd_1055850 120479677566622047937609 := by
  unfold tailWord_1055850
  simp only [CollatzResearch.WordTrace]
  refine ⟨9627503306210812417179251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 25673342149895499779144669 9627503306210812417179251)
  ·
    refine ⟨14441254959316218625768877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9627503306210812417179251 14441254959316218625768877)
    ·
      refine ⟨5415470609743581984663329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14441254959316218625768877 5415470609743581984663329)
      ·
        refine ⟨4061602957307686488497497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5415470609743581984663329 4061602957307686488497497)
        ·
          refine ⟨3046202217980764866373123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4061602957307686488497497 3046202217980764866373123)
          ·
            refine ⟨4569303326971147299559685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3046202217980764866373123 4569303326971147299559685)
            ·
              refine ⟨856744373807090118667441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4569303326971147299559685 856744373807090118667441)
              ·
                refine ⟨642558280355317589000581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 856744373807090118667441 642558280355317589000581)
                ·
                  refine ⟨120479677566622047937609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 642558280355317589000581 120479677566622047937609)
                  ·
                    rfl

theorem cell22_1055850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 4, 2, 4].length) (baseStart_1055850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055850 prefixEnd_1055850 := by exact prefixLift 1055850
  have htrace : WordTrace (prefixWord ++ tailWord_1055850) baseStart_1055850 baseEnd_1055850 := by
    simpa [prefixWord, tailWord_1055850, baseEnd_1055850] using wordTrace_append hprefix tailTrace_1055850
  have hstable : (prefixWord ++ tailWord_1055850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055850).length < 2 ^ (prefixWord ++ tailWord_1055850).sum := by decide
  have hdescent : baseEnd_1055850 < baseStart_1055850 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055880 : List Nat := [2, 1, 3, 4, 2, 2, 1, 1, 2, 4]
def baseStart_1055880 : Nat := 118140960795 + 1055880 * 2 ^ 59
def prefixEnd_1055880 : Nat := 4983230072969 + 3 ^ 40 * 1055880 * 2
def baseEnd_1055880 : Nat := 361449302312956065562735

theorem tailTrace_1055880 : CollatzResearch.WordTrace tailWord_1055880 prefixEnd_1055880 361449302312956065562735 := by
  unfold tailWord_1055880
  simp only [CollatzResearch.WordTrace]
  refine ⟨19255553707367282396154547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25674071609823043194872729 19255553707367282396154547)
  ·
    refine ⟨28883330561050923594231821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19255553707367282396154547 28883330561050923594231821)
    ·
      refine ⟨10831248960394096347836933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28883330561050923594231821 10831248960394096347836933)
      ·
        refine ⟨2030859180073893065219425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10831248960394096347836933 2030859180073893065219425)
        ·
          refine ⟨1523144385055419798914569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2030859180073893065219425 1523144385055419798914569)
          ·
            refine ⟨1142358288791564849185927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1523144385055419798914569 1142358288791564849185927)
            ·
              refine ⟨1713537433187347273778891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142358288791564849185927 1713537433187347273778891)
              ·
                refine ⟨2570306149781020910668337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713537433187347273778891 2570306149781020910668337)
                ·
                  refine ⟨1927729612335765683001253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2570306149781020910668337 1927729612335765683001253)
                  ·
                    refine ⟨361449302312956065562735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1927729612335765683001253 361449302312956065562735)
                    ·
                      rfl

theorem cell22_1055880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_1055880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055880 prefixEnd_1055880 := by exact prefixLift 1055880
  have htrace : WordTrace (prefixWord ++ tailWord_1055880) baseStart_1055880 baseEnd_1055880 := by
    simpa [prefixWord, tailWord_1055880, baseEnd_1055880] using wordTrace_append hprefix tailTrace_1055880
  have hstable : (prefixWord ++ tailWord_1055880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055880).length < 2 ^ (prefixWord ++ tailWord_1055880).sum := by decide
  have hdescent : baseEnd_1055880 < baseStart_1055880 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1055968 : List Nat := [2, 1, 1, 3, 1, 6, 1, 1, 6]
def baseStart_1055968 : Nat := 118140960795 + 1055968 * 2 ^ 59
def prefixEnd_1055968 : Nat := 4983230072969 + 3 ^ 40 * 1055968 * 2
def baseEnd_1055968 : Nat := 120493142170451056454155

theorem tailTrace_1055968 : CollatzResearch.WordTrace tailWord_1055968 prefixEnd_1055968 120493142170451056454155 := by
  unfold tailWord_1055968
  simp only [CollatzResearch.WordTrace]
  refine ⟨19257158519207877910756279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25676211358943837214341705 19257158519207877910756279)
  ·
    refine ⟨28885737778811816866134419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19257158519207877910756279 28885737778811816866134419)
    ·
      refine ⟨43328606668217725299201629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28885737778811816866134419 43328606668217725299201629)
      ·
        refine ⟨16248227500581646987200611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43328606668217725299201629 16248227500581646987200611)
        ·
          refine ⟨24372341250872470480800917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16248227500581646987200611 24372341250872470480800917)
          ·
            refine ⟨1142453496134647053787543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 24372341250872470480800917 1142453496134647053787543)
            ·
              refine ⟨1713680244201970580681315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142453496134647053787543 1713680244201970580681315)
              ·
                refine ⟨2570520366302955871021973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713680244201970580681315 2570520366302955871021973)
                ·
                  refine ⟨120493142170451056454155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2570520366302955871021973 120493142170451056454155)
                  ·
                    rfl

theorem cell22_1055968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 1, 1, 6].length) (baseStart_1055968 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1055968 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1055968 prefixEnd_1055968 := by exact prefixLift 1055968
  have htrace : WordTrace (prefixWord ++ tailWord_1055968) baseStart_1055968 baseEnd_1055968 := by
    simpa [prefixWord, tailWord_1055968, baseEnd_1055968] using wordTrace_append hprefix tailTrace_1055968
  have hstable : (prefixWord ++ tailWord_1055968).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1055968).length < 2 ^ (prefixWord ++ tailWord_1055968).sum := by decide
  have hdescent : baseEnd_1055968 < baseStart_1055968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1055968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056056 : List Nat := [2, 1, 2, 1, 3, 1, 1, 1, 3, 7]
def baseStart_1056056 : Nat := 118140960795 + 1056056 * 2 ^ 59
def prefixEnd_1056056 : Nat := 4983230072969 + 3 ^ 40 * 1056056 * 2
def baseEnd_1056056 : Nat := 361509550709750273162195

theorem tailTrace_1056056 : CollatzResearch.WordTrace tailWord_1056056 prefixEnd_1056056 361509550709750273162195 := by
  unfold tailWord_1056056
  simp only [CollatzResearch.WordTrace]
  refine ⟨19258763331048473425358011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25678351108064631233810681 19258763331048473425358011)
  ·
    refine ⟨28888144996572710138037017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19258763331048473425358011 28888144996572710138037017)
    ·
      refine ⟨21666108747429532603527763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28888144996572710138037017 21666108747429532603527763)
      ·
        refine ⟨32499163121144298905291645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21666108747429532603527763 32499163121144298905291645)
        ·
          refine ⟨12187186170429112089484367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32499163121144298905291645 12187186170429112089484367)
          ·
            refine ⟨18280779255643668134226551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12187186170429112089484367 18280779255643668134226551)
            ·
              refine ⟨27421168883465502201339827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18280779255643668134226551 27421168883465502201339827)
              ·
                refine ⟨41131753325198253302009741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27421168883465502201339827 41131753325198253302009741)
                ·
                  refine ⟨15424407496949344988253653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 41131753325198253302009741 15424407496949344988253653)
                  ·
                    refine ⟨361509550709750273162195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 15424407496949344988253653 361509550709750273162195)
                    ·
                      rfl

theorem cell22_1056056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 1, 3, 7].length) (baseStart_1056056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056056 prefixEnd_1056056 := by exact prefixLift 1056056
  have htrace : WordTrace (prefixWord ++ tailWord_1056056) baseStart_1056056 baseEnd_1056056 := by
    simpa [prefixWord, tailWord_1056056, baseEnd_1056056] using wordTrace_append hprefix tailTrace_1056056
  have hstable : (prefixWord ++ tailWord_1056056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056056).length < 2 ^ (prefixWord ++ tailWord_1056056).sum := by decide
  have hdescent : baseEnd_1056056 < baseStart_1056056 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056133 : List Nat := [1, 3, 1, 1, 3, 1, 3, 1, 4, 4]
def baseStart_1056133 : Nat := 118140960795 + 1056133 * 2 ^ 59
def prefixEnd_1056133 : Nat := 4983230072969 + 3 ^ 40 * 1056133 * 2
def baseEnd_1056133 : Nat := 361535909383347738986959

theorem tailTrace_1056133 : CollatzResearch.WordTrace tailWord_1056133 prefixEnd_1056133 361535909383347738986959 := by
  unfold tailWord_1056133
  simp only [CollatzResearch.WordTrace]
  refine ⟨38520335082817989001269053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25680223388545326000846035 38520335082817989001269053)
  ·
    refine ⟨14445125656056745875475895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38520335082817989001269053 14445125656056745875475895)
    ·
      refine ⟨21667688484085118813213843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14445125656056745875475895 21667688484085118813213843)
      ·
        refine ⟨32501532726127678219820765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21667688484085118813213843 32501532726127678219820765)
        ·
          refine ⟨12188074772297879332432787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32501532726127678219820765 12188074772297879332432787)
          ·
            refine ⟨18282112158446818998649181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12188074772297879332432787 18282112158446818998649181)
            ·
              refine ⟨6855792059417557124493443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18282112158446818998649181 6855792059417557124493443)
              ·
                refine ⟨10283688089126335686740165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6855792059417557124493443 10283688089126335686740165)
                ·
                  refine ⟨1928191516711187941263781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 10283688089126335686740165 1928191516711187941263781)
                  ·
                    refine ⟨361535909383347738986959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1928191516711187941263781 361535909383347738986959)
                    ·
                      rfl

theorem cell22_1056133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 3, 1, 4, 4].length) (baseStart_1056133 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056133 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056133 prefixEnd_1056133 := by exact prefixLift 1056133
  have htrace : WordTrace (prefixWord ++ tailWord_1056133) baseStart_1056133 baseEnd_1056133 := by
    simpa [prefixWord, tailWord_1056133, baseEnd_1056133] using wordTrace_append hprefix tailTrace_1056133
  have hstable : (prefixWord ++ tailWord_1056133).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056133).length < 2 ^ (prefixWord ++ tailWord_1056133).sum := by decide
  have hdescent : baseEnd_1056133 < baseStart_1056133 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056135 : List Nat := [1, 1, 4, 2, 2, 2, 2, 1, 4, 3]
def baseStart_1056135 : Nat := 118140960795 + 1056135 * 2 ^ 59
def prefixEnd_1056135 : Nat := 4983230072969 + 3 ^ 40 * 1056135 * 2
def baseEnd_1056135 : Nat := 361536594024220400436953

theorem tailTrace_1056135 : CollatzResearch.WordTrace tailWord_1056135 prefixEnd_1056135 361536594024220400436953 := by
  unfold tailWord_1056135
  simp only [CollatzResearch.WordTrace]
  refine ⟨38520408028810743342841859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25680272019207162228561239 38520408028810743342841859)
  ·
    refine ⟨57780612043216115014262789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38520408028810743342841859 57780612043216115014262789)
    ·
      refine ⟨10833864758103021565174273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57780612043216115014262789 10833864758103021565174273)
      ·
        refine ⟨8125398568577266173880705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10833864758103021565174273 8125398568577266173880705)
        ·
          refine ⟨6094048926432949630410529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8125398568577266173880705 6094048926432949630410529)
          ·
            refine ⟨4570536694824712222807897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6094048926432949630410529 4570536694824712222807897)
            ·
              refine ⟨3427902521118534167105923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4570536694824712222807897 3427902521118534167105923)
              ·
                refine ⟨5141853781677801250658885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3427902521118534167105923 5141853781677801250658885)
                ·
                  refine ⟨964097584064587734498541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 5141853781677801250658885 964097584064587734498541)
                  ·
                    refine ⟨361536594024220400436953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964097584064587734498541 361536594024220400436953)
                    ·
                      rfl

theorem cell22_1056135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 2, 1, 4, 3].length) (baseStart_1056135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056135 prefixEnd_1056135 := by exact prefixLift 1056135
  have htrace : WordTrace (prefixWord ++ tailWord_1056135) baseStart_1056135 baseEnd_1056135 := by
    simpa [prefixWord, tailWord_1056135, baseEnd_1056135] using wordTrace_append hprefix tailTrace_1056135
  have hstable : (prefixWord ++ tailWord_1056135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056135).length < 2 ^ (prefixWord ++ tailWord_1056135).sum := by decide
  have hdescent : baseEnd_1056135 < baseStart_1056135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056137 : List Nat := [1, 2, 1, 1, 8, 1, 1, 1, 6]
def baseStart_1056137 : Nat := 118140960795 + 1056137 * 2 ^ 59
def prefixEnd_1056137 : Nat := 4983230072969 + 3 ^ 40 * 1056137 * 2
def baseEnd_1056137 : Nat := 120512426221697687295649

theorem tailTrace_1056137 : CollatzResearch.WordTrace tailWord_1056137 prefixEnd_1056137 120512426221697687295649 := by
  unfold tailWord_1056137
  simp only [CollatzResearch.WordTrace]
  refine ⟨38520480974803497684414665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 25680320649868998456276443 38520480974803497684414665)
  ·
    refine ⟨28890360731102623263310999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38520480974803497684414665 28890360731102623263310999)
    ·
      refine ⟨43335541096653934894966499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28890360731102623263310999 43335541096653934894966499)
      ·
        refine ⟨65003311644980902342449749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43335541096653934894966499 65003311644980902342449749)
        ·
          refine ⟨761757558339619949325583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 65003311644980902342449749 761757558339619949325583)
          ·
            refine ⟨1142636337509429923988375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761757558339619949325583 1142636337509429923988375)
            ·
              refine ⟨1713954506264144885982563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142636337509429923988375 1713954506264144885982563)
              ·
                refine ⟨2570931759396217328973845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1713954506264144885982563 2570931759396217328973845)
                ·
                  refine ⟨120512426221697687295649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2570931759396217328973845 120512426221697687295649)
                  ·
                    rfl

theorem cell22_1056137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 1, 1, 6].length) (baseStart_1056137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056137 prefixEnd_1056137 := by exact prefixLift 1056137
  have htrace : WordTrace (prefixWord ++ tailWord_1056137) baseStart_1056137 baseEnd_1056137 := by
    simpa [prefixWord, tailWord_1056137, baseEnd_1056137] using wordTrace_append hprefix tailTrace_1056137
  have hstable : (prefixWord ++ tailWord_1056137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056137).length < 2 ^ (prefixWord ++ tailWord_1056137).sum := by decide
  have hdescent : baseEnd_1056137 < baseStart_1056137 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056156 : List Nat := [2, 2, 3, 4, 2, 1, 1, 2, 1, 4]
def baseStart_1056156 : Nat := 118140960795 + 1056156 * 2 ^ 59
def prefixEnd_1056156 : Nat := 4983230072969 + 3 ^ 40 * 1056156 * 2
def baseEnd_1056156 : Nat := 361543782753383345661889

theorem tailTrace_1056156 : CollatzResearch.WordTrace tailWord_1056156 prefixEnd_1056156 361543782753383345661889 := by
  unfold tailWord_1056156
  simp only [CollatzResearch.WordTrace]
  refine ⟨19260586980867331964678161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25680782641156442619570881 19260586980867331964678161)
  ·
    refine ⟨14445440235650498973508621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19260586980867331964678161 14445440235650498973508621)
    ·
      refine ⟨5417040088368937115065733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14445440235650498973508621 5417040088368937115065733)
      ·
        refine ⟨1015695016569175709074825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5417040088368937115065733 1015695016569175709074825)
        ·
          refine ⟨761771262426881781806119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1015695016569175709074825 761771262426881781806119)
          ·
            refine ⟨1142656893640322672709179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 761771262426881781806119 1142656893640322672709179)
            ·
              refine ⟨1713985340460484009063769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1142656893640322672709179 1713985340460484009063769)
              ·
                refine ⟨1285489005345363006797827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1713985340460484009063769 1285489005345363006797827)
                ·
                  refine ⟨1928233508018044510196741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1285489005345363006797827 1928233508018044510196741)
                  ·
                    refine ⟨361543782753383345661889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1928233508018044510196741 361543782753383345661889)
                    ·
                      rfl

theorem cell22_1056156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 1, 2, 1, 4].length) (baseStart_1056156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056156 prefixEnd_1056156 := by exact prefixLift 1056156
  have htrace : WordTrace (prefixWord ++ tailWord_1056156) baseStart_1056156 baseEnd_1056156 := by
    simpa [prefixWord, tailWord_1056156, baseEnd_1056156] using wordTrace_append hprefix tailTrace_1056156
  have hstable : (prefixWord ++ tailWord_1056156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056156).length < 2 ^ (prefixWord ++ tailWord_1056156).sum := by decide
  have hdescent : baseEnd_1056156 < baseStart_1056156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056208 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 2, 5]
def baseStart_1056208 : Nat := 118140960795 + 1056208 * 2 ^ 59
def prefixEnd_1056208 : Nat := 4983230072969 + 3 ^ 40 * 1056208 * 2
def baseEnd_1056208 : Nat := 361561583416072543361729

theorem tailTrace_1056208 : CollatzResearch.WordTrace tailWord_1056208 prefixEnd_1056208 361561583416072543361729 := by
  unfold tailWord_1056208
  simp only [CollatzResearch.WordTrace]
  refine ⟨19261535278773138405124639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 25682047038364184540166185 19261535278773138405124639)
  ·
    refine ⟨28892302918159707607686959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19261535278773138405124639 28892302918159707607686959)
    ·
      refine ⟨43338454377239561411530439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28892302918159707607686959 43338454377239561411530439)
      ·
        refine ⟨65007681565859342117295659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43338454377239561411530439 65007681565859342117295659)
        ·
          refine ⟨97511522348789013175943489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 65007681565859342117295659 97511522348789013175943489)
          ·
            refine ⟨73133641761591759881957617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 97511522348789013175943489 73133641761591759881957617)
            ·
              refine ⟨54850231321193819911468213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 73133641761591759881957617 54850231321193819911468213)
              ·
                refine ⟨5142209186361920616700145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54850231321193819911468213 5142209186361920616700145)
                ·
                  refine ⟨3856656889771440462525109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5142209186361920616700145 3856656889771440462525109)
                  ·
                    refine ⟨361561583416072543361729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3856656889771440462525109 361561583416072543361729)
                    ·
                      rfl

theorem cell22_1056208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 2, 5].length) (baseStart_1056208 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056208 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056208 prefixEnd_1056208 := by exact prefixLift 1056208
  have htrace : WordTrace (prefixWord ++ tailWord_1056208) baseStart_1056208 baseEnd_1056208 := by
    simpa [prefixWord, tailWord_1056208, baseEnd_1056208] using wordTrace_append hprefix tailTrace_1056208
  have hstable : (prefixWord ++ tailWord_1056208).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056208).length < 2 ^ (prefixWord ++ tailWord_1056208).sum := by decide
  have hdescent : baseEnd_1056208 < baseStart_1056208 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1056214 : List Nat := [5, 2, 1, 1, 1, 3, 1, 2, 3, 3]
def baseStart_1056214 : Nat := 118140960795 + 1056214 * 2 ^ 59
def prefixEnd_1056214 : Nat := 4983230072969 + 3 ^ 40 * 1056214 * 2
def baseEnd_1056214 : Nat := 361563637338690527711711

theorem tailTrace_1056214 : CollatzResearch.WordTrace tailWord_1056214 prefixEnd_1056214 361563637338690527711711 := by
  unfold tailWord_1056214
  simp only [CollatzResearch.WordTrace]
  refine ⟨2407705587220283739685481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 25682192930349693223311797 2407705587220283739685481)
  ·
    refine ⟨1805779190415212804764111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2407705587220283739685481 1805779190415212804764111)
    ·
      refine ⟨2708668785622819207146167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1805779190415212804764111 2708668785622819207146167)
      ·
        refine ⟨4063003178434228810719251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2708668785622819207146167 4063003178434228810719251)
        ·
          refine ⟨6094504767651343216078877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4063003178434228810719251 6094504767651343216078877)
          ·
            refine ⟨2285439287869253706029579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6094504767651343216078877 2285439287869253706029579)
            ·
              refine ⟨3428158931803880559044369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2285439287869253706029579 3428158931803880559044369)
              ·
                refine ⟨2571119198852910419283277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3428158931803880559044369 2571119198852910419283277)
                ·
                  refine ⟨964169699569841407231229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2571119198852910419283277 964169699569841407231229)
                  ·
                    refine ⟨361563637338690527711711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 964169699569841407231229 361563637338690527711711)
                    ·
                      rfl

theorem cell22_1056214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_1056214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_1056214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_1056214 prefixEnd_1056214 := by exact prefixLift 1056214
  have htrace : WordTrace (prefixWord ++ tailWord_1056214) baseStart_1056214 baseEnd_1056214 := by
    simpa [prefixWord, tailWord_1056214, baseEnd_1056214] using wordTrace_append hprefix tailTrace_1056214
  have hstable : (prefixWord ++ tailWord_1056214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1056214).length < 2 ^ (prefixWord ++ tailWord_1056214).sum := by decide
  have hdescent : baseEnd_1056214 < baseStart_1056214 := by decide
  rcases family_descends (prefixWord ++ tailWord_1056214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
