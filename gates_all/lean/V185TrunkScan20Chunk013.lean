import V185TrunkScan20Chunk012

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental

namespace V185TrunkScan20Incremental

def tailWord_78838 : List Nat := [5, 1, 1, 1, 3, 2, 3, 1, 3]
def baseStart_78838 : Nat := 118140960795 + 78838 * 2 ^ 59
def prefixEnd_78838 : Nat := 4983230072969 + 3 ^ 40 * 78838 * 2
def baseEnd_78838 : Nat := 35983811412682470811055

theorem tailTrace_78838 : CollatzResearch.WordTrace tailWord_78838 prefixEnd_78838 35983811412682470811055 := by
  unfold tailWord_78838
  simp only [CollatzResearch.WordTrace]
  refine ⟨179716130524429081471823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1916972058927243535699445 179716130524429081471823)
  ·
    refine ⟨269574195786643622207735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179716130524429081471823 269574195786643622207735)
    ·
      refine ⟨404361293679965433311603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 269574195786643622207735 404361293679965433311603)
      ·
        refine ⟨606541940519948149967405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404361293679965433311603 606541940519948149967405)
        ·
          refine ⟨227453227694980556237777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 606541940519948149967405 227453227694980556237777)
          ·
            refine ⟨170589920771235417178333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 227453227694980556237777 170589920771235417178333)
            ·
              refine ⟨63971220289213281441875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170589920771235417178333 63971220289213281441875)
              ·
                refine ⟨95956830433819922162813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63971220289213281441875 95956830433819922162813)
                ·
                  refine ⟨35983811412682470811055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95956830433819922162813 35983811412682470811055)
                  ·
                    rfl

theorem cell20_78838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 3, 1, 3].length) (baseStart_78838 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78838 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78838 prefixEnd_78838 := by exact prefixLift 78838
  have htrace : WordTrace (prefixWord ++ tailWord_78838) baseStart_78838 baseEnd_78838 := by
    simpa [prefixWord, tailWord_78838, baseEnd_78838] using wordTrace_append hprefix tailTrace_78838
  have hstable : (prefixWord ++ tailWord_78838).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78838).length < 2 ^ (prefixWord ++ tailWord_78838).sum := by decide
  have hdescent : baseEnd_78838 < baseStart_78838 := by decide
  rcases family_descends (prefixWord ++ tailWord_78838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78849 : List Nat := [1, 2, 4, 1, 2, 2, 2, 2, 4]
def baseStart_78849 : Nat := 118140960795 + 78849 * 2 ^ 59
def prefixEnd_78849 : Nat := 4983230072969 + 3 ^ 40 * 78849 * 2
def baseEnd_78849 : Nat := 35988832112415321444343

theorem tailTrace_78849 : CollatzResearch.WordTrace tailWord_78849 prefixEnd_78849 35988832112415321444343 := by
  unfold tailWord_78849
  simp only [CollatzResearch.WordTrace]
  refine ⟨2875859291351014182199601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1917239527567342788133067 2875859291351014182199601)
  ·
    refine ⟨2156894468513260636649701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2875859291351014182199601 2156894468513260636649701)
    ·
      refine ⟨404417712846236369371819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2156894468513260636649701 404417712846236369371819)
      ·
        refine ⟨606626569269354554057729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 404417712846236369371819 606626569269354554057729)
        ·
          refine ⟨454969926952015915543297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 606626569269354554057729 454969926952015915543297)
          ·
            refine ⟨341227445214011936657473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 454969926952015915543297 341227445214011936657473)
            ·
              refine ⟨255920583910508952493105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341227445214011936657473 255920583910508952493105)
              ·
                refine ⟨191940437932881714369829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 255920583910508952493105 191940437932881714369829)
                ·
                  refine ⟨35988832112415321444343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 191940437932881714369829 35988832112415321444343)
                  ·
                    rfl

theorem cell20_78849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 2, 2, 2, 4].length) (baseStart_78849 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78849 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78849 prefixEnd_78849 := by exact prefixLift 78849
  have htrace : WordTrace (prefixWord ++ tailWord_78849) baseStart_78849 baseEnd_78849 := by
    simpa [prefixWord, tailWord_78849, baseEnd_78849] using wordTrace_append hprefix tailTrace_78849
  have hstable : (prefixWord ++ tailWord_78849).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78849).length < 2 ^ (prefixWord ++ tailWord_78849).sum := by decide
  have hdescent : baseEnd_78849 < baseStart_78849 := by decide
  rcases family_descends (prefixWord ++ tailWord_78849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78856 : List Nat := [2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_78856 : Nat := 118140960795 + 78856 * 2 ^ 59
def prefixEnd_78856 : Nat := 4983230072969 + 3 ^ 40 * 78856 * 2
def baseEnd_78856 : Nat := 11997342367718136070327

theorem tailTrace_78856 : CollatzResearch.WordTrace tailWord_78856 prefixEnd_78856 11997342367718136070327 := by
  unfold tailWord_78856
  simp only [CollatzResearch.WordTrace]
  refine ⟨1438057301162827188852211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1917409734883769585136281 1438057301162827188852211)
  ·
    refine ⟨2157085951744240783278317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1438057301162827188852211 2157085951744240783278317)
    ·
      refine ⟨808907231904090293729369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2157085951744240783278317 808907231904090293729369)
      ·
        refine ⟨606680423928067720297027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 808907231904090293729369 606680423928067720297027)
        ·
          refine ⟨910020635892101580445541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 606680423928067720297027 910020635892101580445541)
          ·
            refine ⟨170628869229769046333539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 910020635892101580445541 170628869229769046333539)
            ·
              refine ⟨255943303844653569500309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170628869229769046333539 255943303844653569500309)
              ·
                refine ⟨11997342367718136070327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 255943303844653569500309 11997342367718136070327)
                ·
                  rfl

theorem cell20_78856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_78856 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78856 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78856 prefixEnd_78856 := by exact prefixLift 78856
  have htrace : WordTrace (prefixWord ++ tailWord_78856) baseStart_78856 baseEnd_78856 := by
    simpa [prefixWord, tailWord_78856, baseEnd_78856] using wordTrace_append hprefix tailTrace_78856
  have hstable : (prefixWord ++ tailWord_78856).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78856).length < 2 ^ (prefixWord ++ tailWord_78856).sum := by decide
  have hdescent : baseEnd_78856 < baseStart_78856 := by decide
  rcases family_descends (prefixWord ++ tailWord_78856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78883 : List Nat := [1, 1, 1, 4, 3, 3, 3, 2, 2]
def baseStart_78883 : Nat := 118140960795 + 78883 * 2 ^ 59
def prefixEnd_78883 : Nat := 4983230072969 + 3 ^ 40 * 78883 * 2
def baseEnd_78883 : Nat := 36004350638862314310871

theorem tailTrace_78883 : CollatzResearch.WordTrace tailWord_78883 prefixEnd_78883 36004350638862314310871 := by
  unfold tailWord_78883
  simp only [CollatzResearch.WordTrace]
  refine ⟨2877099373227837988937303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1918066248818558659291535 2877099373227837988937303)
  ·
    refine ⟨4315649059841756983405955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2877099373227837988937303 4315649059841756983405955)
    ·
      refine ⟨6473473589762635475108933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4315649059841756983405955 6473473589762635475108933)
      ·
        refine ⟨1213776298080494151582925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6473473589762635475108933 1213776298080494151582925)
        ·
          refine ⟨455166111780185306843597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1213776298080494151582925 455166111780185306843597)
          ·
            refine ⟨170687291917569490066349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455166111780185306843597 170687291917569490066349)
            ·
              refine ⟨64007734469088558774881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170687291917569490066349 64007734469088558774881)
              ·
                refine ⟨48005800851816419081161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64007734469088558774881 48005800851816419081161)
                ·
                  refine ⟨36004350638862314310871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48005800851816419081161 36004350638862314310871)
                  ·
                    rfl

theorem cell20_78883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 3, 2, 2].length) (baseStart_78883 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78883 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78883 prefixEnd_78883 := by exact prefixLift 78883
  have htrace : WordTrace (prefixWord ++ tailWord_78883) baseStart_78883 baseEnd_78883 := by
    simpa [prefixWord, tailWord_78883, baseEnd_78883] using wordTrace_append hprefix tailTrace_78883
  have hstable : (prefixWord ++ tailWord_78883).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78883).length < 2 ^ (prefixWord ++ tailWord_78883).sum := by decide
  have hdescent : baseEnd_78883 < baseStart_78883 := by decide
  rcases family_descends (prefixWord ++ tailWord_78883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78915 : List Nat := [1, 1, 1, 3, 1, 2, 3, 8]
def baseStart_78915 : Nat := 118140960795 + 78915 * 2 ^ 59
def prefixEnd_78915 : Nat := 4983230072969 + 3 ^ 40 * 78915 * 2
def baseEnd_78915 : Nat := 12006318770270808414691

theorem tailTrace_78915 : CollatzResearch.WordTrace tailWord_78915 prefixEnd_78915 12006318770270808414691 := by
  unfold tailWord_78915
  simp only [CollatzResearch.WordTrace]
  refine ⟨2878266509111907454102199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1918844339407938302734799 2878266509111907454102199)
  ·
    refine ⟨4317399763667861181153299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2878266509111907454102199 4317399763667861181153299)
    ·
      refine ⟨6476099645501791771729949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4317399763667861181153299 6476099645501791771729949)
      ·
        refine ⟨2428537367063171914398731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6476099645501791771729949 2428537367063171914398731)
        ·
          refine ⟨3642806050594757871598097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2428537367063171914398731 3642806050594757871598097)
          ·
            refine ⟨2732104537946068403698573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3642806050594757871598097 2732104537946068403698573)
            ·
              refine ⟨1024539201729775651386965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2732104537946068403698573 1024539201729775651386965)
              ·
                refine ⟨12006318770270808414691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1024539201729775651386965 12006318770270808414691)
                ·
                  rfl

theorem cell20_78915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 3, 8].length) (baseStart_78915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78915 prefixEnd_78915 := by exact prefixLift 78915
  have htrace : WordTrace (prefixWord ++ tailWord_78915) baseStart_78915 baseEnd_78915 := by
    simpa [prefixWord, tailWord_78915, baseEnd_78915] using wordTrace_append hprefix tailTrace_78915
  have hstable : (prefixWord ++ tailWord_78915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78915).length < 2 ^ (prefixWord ++ tailWord_78915).sum := by decide
  have hdescent : baseEnd_78915 < baseStart_78915 := by decide
  rcases family_descends (prefixWord ++ tailWord_78915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78934 : List Nat := [5, 2, 2, 1, 2, 2, 2, 2, 2]
def baseStart_78934 : Nat := 118140960795 + 78934 * 2 ^ 59
def prefixEnd_78934 : Nat := 4983230072969 + 3 ^ 40 * 78934 * 2
def baseEnd_78934 : Nat := 36027628428532803610663

theorem tailTrace_78934 : CollatzResearch.WordTrace tailWord_78934 prefixEnd_78934 36027628428532803610663 := by
  unfold tailWord_78934
  simp only [CollatzResearch.WordTrace]
  refine ⟨179934968502692106190241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1919306330695382466029237 179934968502692106190241)
  ·
    refine ⟨134951226377019079642681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179934968502692106190241 134951226377019079642681)
    ·
      refine ⟨101213419782764309732011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134951226377019079642681 101213419782764309732011)
      ·
        refine ⟨151820129674146464598017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101213419782764309732011 151820129674146464598017)
        ·
          refine ⟨113865097255609848448513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151820129674146464598017 113865097255609848448513)
          ·
            refine ⟨85398822941707386336385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113865097255609848448513 85398822941707386336385)
            ·
              refine ⟨64049117206280539752289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85398822941707386336385 64049117206280539752289)
              ·
                refine ⟨48036837904710404814217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64049117206280539752289 48036837904710404814217)
                ·
                  refine ⟨36027628428532803610663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48036837904710404814217 36027628428532803610663)
                  ·
                    rfl

theorem cell20_78934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 2, 2, 2, 2].length) (baseStart_78934 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78934 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78934 prefixEnd_78934 := by exact prefixLift 78934
  have htrace : WordTrace (prefixWord ++ tailWord_78934) baseStart_78934 baseEnd_78934 := by
    simpa [prefixWord, tailWord_78934, baseEnd_78934] using wordTrace_append hprefix tailTrace_78934
  have hstable : (prefixWord ++ tailWord_78934).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78934).length < 2 ^ (prefixWord ++ tailWord_78934).sum := by decide
  have hdescent : baseEnd_78934 < baseStart_78934 := by decide
  rcases family_descends (prefixWord ++ tailWord_78934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78980 : List Nat := [2, 3, 2, 1, 2, 2, 1, 5, 2]
def baseStart_78980 : Nat := 118140960795 + 78980 * 2 ^ 59
def prefixEnd_78980 : Nat := 4983230072969 + 3 ^ 40 * 78980 * 2
def baseEnd_78980 : Nat := 36048624081961088077141

theorem tailTrace_78980 : CollatzResearch.WordTrace tailWord_78980 prefixEnd_78980 36048624081961088077141 := by
  unfold tailWord_78980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1440318626938211777609197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1920424835917615703478929 1440318626938211777609197)
  ·
    refine ⟨540119485101829416603449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1440318626938211777609197 540119485101829416603449)
    ·
      refine ⟨405089613826372062452587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540119485101829416603449 405089613826372062452587)
      ·
        refine ⟨607634420739558093678881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405089613826372062452587 607634420739558093678881)
        ·
          refine ⟨455725815554668570259161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 607634420739558093678881 455725815554668570259161)
          ·
            refine ⟨341794361666001427694371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 455725815554668570259161 341794361666001427694371)
            ·
              refine ⟨512691542499002141541557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 341794361666001427694371 512691542499002141541557)
              ·
                refine ⟨48064832109281450769521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 512691542499002141541557 48064832109281450769521)
                ·
                  refine ⟨36048624081961088077141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48064832109281450769521 36048624081961088077141)
                  ·
                    rfl

theorem cell20_78980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 1, 5, 2].length) (baseStart_78980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78980 prefixEnd_78980 := by exact prefixLift 78980
  have htrace : WordTrace (prefixWord ++ tailWord_78980) baseStart_78980 baseEnd_78980 := by
    simpa [prefixWord, tailWord_78980, baseEnd_78980] using wordTrace_append hprefix tailTrace_78980
  have hstable : (prefixWord ++ tailWord_78980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78980).length < 2 ^ (prefixWord ++ tailWord_78980).sum := by decide
  have hdescent : baseEnd_78980 < baseStart_78980 := by decide
  rcases family_descends (prefixWord ++ tailWord_78980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_78994 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 5]
def baseStart_78994 : Nat := 118140960795 + 78994 * 2 ^ 59
def prefixEnd_78994 : Nat := 4983230072969 + 3 ^ 40 * 78994 * 2
def baseEnd_78994 : Nat := 36055014063439261610417

theorem tailTrace_78994 : CollatzResearch.WordTrace tailWord_78994 prefixEnd_78994 36055014063439261610417 := by
  unfold tailWord_78994
  simp only [CollatzResearch.WordTrace]
  refine ⟨720286968956425986557009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1920765250550469297485357 720286968956425986557009)
  ·
    refine ⟨540215226717319489917757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 720286968956425986557009 540215226717319489917757)
    ·
      refine ⟨202580710018994808719159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 540215226717319489917757 202580710018994808719159)
      ·
        refine ⟨303871065028492213078739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202580710018994808719159 303871065028492213078739)
        ·
          refine ⟨455806597542738319618109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 303871065028492213078739 455806597542738319618109)
          ·
            refine ⟨170927474078526869856791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 455806597542738319618109 170927474078526869856791)
            ·
              refine ⟨256391211117790304785187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170927474078526869856791 256391211117790304785187)
              ·
                refine ⟨384586816676685457177781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256391211117790304785187 384586816676685457177781)
                ·
                  refine ⟨36055014063439261610417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 384586816676685457177781 36055014063439261610417)
                  ·
                    rfl

theorem cell20_78994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_78994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_78994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_78994 prefixEnd_78994 := by exact prefixLift 78994
  have htrace : WordTrace (prefixWord ++ tailWord_78994) baseStart_78994 baseEnd_78994 := by
    simpa [prefixWord, tailWord_78994, baseEnd_78994] using wordTrace_append hprefix tailTrace_78994
  have hstable : (prefixWord ++ tailWord_78994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_78994).length < 2 ^ (prefixWord ++ tailWord_78994).sum := by decide
  have hdescent : baseEnd_78994 < baseStart_78994 := by decide
  rcases family_descends (prefixWord ++ tailWord_78994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79018 : List Nat := [3, 1, 5, 1, 1, 1, 2, 2, 4]
def baseStart_79018 : Nat := 118140960795 + 79018 * 2 ^ 59
def prefixEnd_79018 : Nat := 4983230072969 + 3 ^ 40 * 79018 * 2
def baseEnd_79018 : Nat := 36065968317401844810319

theorem tailTrace_79018 : CollatzResearch.WordTrace tailWord_79018 prefixEnd_79018 36065968317401844810319 := by
  unfold tailWord_79018
  simp only [CollatzResearch.WordTrace]
  refine ⟨720505806934689011275427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1921348818492504030067805 720505806934689011275427)
  ·
    refine ⟨1080758710402033516913141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 720505806934689011275427 1080758710402033516913141)
    ·
      refine ⟨101321129100190642210607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1080758710402033516913141 101321129100190642210607)
      ·
        refine ⟨151981693650285963315911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101321129100190642210607 151981693650285963315911)
        ·
          refine ⟨227972540475428944973867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151981693650285963315911 227972540475428944973867)
          ·
            refine ⟨341958810713143417460801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227972540475428944973867 341958810713143417460801)
            ·
              refine ⟨256469108034857563095601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 341958810713143417460801 256469108034857563095601)
              ·
                refine ⟨192351831026143172321701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 256469108034857563095601 192351831026143172321701)
                ·
                  refine ⟨36065968317401844810319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 192351831026143172321701 36065968317401844810319)
                  ·
                    rfl

theorem cell20_79018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 2, 2, 4].length) (baseStart_79018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79018 prefixEnd_79018 := by exact prefixLift 79018
  have htrace : WordTrace (prefixWord ++ tailWord_79018) baseStart_79018 baseEnd_79018 := by
    simpa [prefixWord, tailWord_79018, baseEnd_79018] using wordTrace_append hprefix tailTrace_79018
  have hstable : (prefixWord ++ tailWord_79018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79018).length < 2 ^ (prefixWord ++ tailWord_79018).sum := by decide
  have hdescent : baseEnd_79018 < baseStart_79018 := by decide
  rcases family_descends (prefixWord ++ tailWord_79018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79021 : List Nat := [1, 5, 2, 1, 4, 1, 2, 4]
def baseStart_79021 : Nat := 118140960795 + 79021 * 2 ^ 59
def prefixEnd_79021 : Nat := 4983230072969 + 3 ^ 40 * 79021 * 2
def baseEnd_79021 : Nat := 12022445866382389236769

theorem tailTrace_79021 : CollatzResearch.WordTrace tailWord_79021 prefixEnd_79021 12022445866382389236769 := by
  unfold tailWord_79021
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882132646727887557460917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1921421764485258371640611 2882132646727887557460917)
  ·
    refine ⟨270199935630739458511961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2882132646727887557460917 270199935630739458511961)
    ·
      refine ⟨202649951723054593883971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 270199935630739458511961 202649951723054593883971)
      ·
        refine ⟨303974927584581890825957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 202649951723054593883971 303974927584581890825957)
        ·
          refine ⟨56995298922109104529867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 303974927584581890825957 56995298922109104529867)
          ·
            refine ⟨85492948383163656794801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56995298922109104529867 85492948383163656794801)
            ·
              refine ⟨64119711287372742596101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85492948383163656794801 64119711287372742596101)
              ·
                refine ⟨12022445866382389236769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64119711287372742596101 12022445866382389236769)
                ·
                  rfl

theorem cell20_79021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_79021 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79021 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79021 prefixEnd_79021 := by exact prefixLift 79021
  have htrace : WordTrace (prefixWord ++ tailWord_79021) baseStart_79021 baseEnd_79021 := by
    simpa [prefixWord, tailWord_79021, baseEnd_79021] using wordTrace_append hprefix tailTrace_79021
  have hstable : (prefixWord ++ tailWord_79021).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79021).length < 2 ^ (prefixWord ++ tailWord_79021).sum := by decide
  have hdescent : baseEnd_79021 < baseStart_79021 := by decide
  rcases family_descends (prefixWord ++ tailWord_79021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79025 : List Nat := [1, 2, 2, 5, 1, 1, 4, 4]
def baseStart_79025 : Nat := 118140960795 + 79025 * 2 ^ 59
def prefixEnd_79025 : Nat := 4983230072969 + 3 ^ 40 * 79025 * 2
def baseEnd_79025 : Nat := 12023054436046977192319

theorem tailTrace_79025 : CollatzResearch.WordTrace tailWord_79025 prefixEnd_79025 12023054436046977192319 := by
  unfold tailWord_79025
  simp only [CollatzResearch.WordTrace]
  refine ⟨2882278538713396240606529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1921519025808930827071019 2882278538713396240606529)
  ·
    refine ⟨2161708904035047180454897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2882278538713396240606529 2161708904035047180454897)
    ·
      refine ⟨1621281678026285385341173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2161708904035047180454897 1621281678026285385341173)
      ·
        refine ⟨151995157314964254875735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1621281678026285385341173 151995157314964254875735)
        ·
          refine ⟨227992735972446382313603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151995157314964254875735 227992735972446382313603)
          ·
            refine ⟨341989103958669573470405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 227992735972446382313603 341989103958669573470405)
            ·
              refine ⟨64122956992250545025701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 341989103958669573470405 64122956992250545025701)
              ·
                refine ⟨12023054436046977192319, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64122956992250545025701 12023054436046977192319)
                ·
                  rfl

theorem cell20_79025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 4, 4].length) (baseStart_79025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79025 prefixEnd_79025 := by exact prefixLift 79025
  have htrace : WordTrace (prefixWord ++ tailWord_79025) baseStart_79025 baseEnd_79025 := by
    simpa [prefixWord, tailWord_79025, baseEnd_79025] using wordTrace_append hprefix tailTrace_79025
  have hstable : (prefixWord ++ tailWord_79025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79025).length < 2 ^ (prefixWord ++ tailWord_79025).sum := by decide
  have hdescent : baseEnd_79025 < baseStart_79025 := by decide
  rcases family_descends (prefixWord ++ tailWord_79025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79062 : List Nat := [5, 2, 1, 2, 3, 1, 2, 1, 3]
def baseStart_79062 : Nat := 118140960795 + 79062 * 2 ^ 59
def prefixEnd_79062 : Nat := 4983230072969 + 3 ^ 40 * 79062 * 2
def baseEnd_79062 : Nat := 36086051116333247343473

theorem tailTrace_79062 : CollatzResearch.WordTrace tailWord_79062 prefixEnd_79062 36086051116333247343473 := by
  unfold tailWord_79062
  simp only [CollatzResearch.WordTrace]
  refine ⟨180226752473709472481465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1922418693052901039802293 180226752473709472481465)
  ·
    refine ⟨135170064355282104361099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 180226752473709472481465 135170064355282104361099)
    ·
      refine ⟨202755096532923156541649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 135170064355282104361099 202755096532923156541649)
      ·
        refine ⟨152066322399692367406237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 202755096532923156541649 152066322399692367406237)
        ·
          refine ⟨57024870899884637777339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 152066322399692367406237 57024870899884637777339)
          ·
            refine ⟨85537306349826956666009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57024870899884637777339 85537306349826956666009)
            ·
              refine ⟨64152979762370217499507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85537306349826956666009 64152979762370217499507)
              ·
                refine ⟨96229469643555326249261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64152979762370217499507 96229469643555326249261)
                ·
                  refine ⟨36086051116333247343473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96229469643555326249261 36086051116333247343473)
                  ·
                    rfl

theorem cell20_79062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_79062 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79062 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79062 prefixEnd_79062 := by exact prefixLift 79062
  have htrace : WordTrace (prefixWord ++ tailWord_79062) baseStart_79062 baseEnd_79062 := by
    simpa [prefixWord, tailWord_79062, baseEnd_79062] using wordTrace_append hprefix tailTrace_79062
  have hstable : (prefixWord ++ tailWord_79062).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79062).length < 2 ^ (prefixWord ++ tailWord_79062).sum := by decide
  have hdescent : baseEnd_79062 < baseStart_79062 := by decide
  rcases family_descends (prefixWord ++ tailWord_79062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79094 : List Nat := [5, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_79094 : Nat := 118140960795 + 79094 * 2 ^ 59
def prefixEnd_79094 : Nat := 4983230072969 + 3 ^ 40 * 79094 * 2
def baseEnd_79094 : Nat := 36100656788283358276675

theorem tailTrace_79094 : CollatzResearch.WordTrace tailWord_79094 prefixEnd_79094 36100656788283358276675 := by
  unfold tailWord_79094
  simp only [CollatzResearch.WordTrace]
  refine ⟨180299698466463814054271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1923196783642280683245557 180299698466463814054271)
  ·
    refine ⟨270449547699695721081407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 180299698466463814054271 270449547699695721081407)
    ·
      refine ⟨405674321549543581622111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 270449547699695721081407 405674321549543581622111)
      ·
        refine ⟨608511482324315372433167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405674321549543581622111 608511482324315372433167)
        ·
          refine ⟨912767223486473058649751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608511482324315372433167 912767223486473058649751)
          ·
            refine ⟨1369150835229709587974627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 912767223486473058649751 1369150835229709587974627)
            ·
              refine ⟨2053726252844564381961941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1369150835229709587974627 2053726252844564381961941)
              ·
                refine ⟨48134209051044477702233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2053726252844564381961941 48134209051044477702233)
                ·
                  refine ⟨36100656788283358276675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48134209051044477702233 36100656788283358276675)
                  ·
                    rfl

theorem cell20_79094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_79094 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79094 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79094 prefixEnd_79094 := by exact prefixLift 79094
  have htrace : WordTrace (prefixWord ++ tailWord_79094) baseStart_79094 baseEnd_79094 := by
    simpa [prefixWord, tailWord_79094, baseEnd_79094] using wordTrace_append hprefix tailTrace_79094
  have hstable : (prefixWord ++ tailWord_79094).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79094).length < 2 ^ (prefixWord ++ tailWord_79094).sum := by decide
  have hdescent : baseEnd_79094 < baseStart_79094 := by decide
  rcases family_descends (prefixWord ++ tailWord_79094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79105 : List Nat := [1, 2, 4, 1, 1, 11]
def baseStart_79105 : Nat := 118140960795 + 79105 * 2 ^ 59
def prefixEnd_79105 : Nat := 4983230072969 + 3 ^ 40 * 79105 * 2
def baseEnd_79105 : Nat := 1337247314370970700369

theorem tailTrace_79105 : CollatzResearch.WordTrace tailWord_79105 prefixEnd_79105 1337247314370970700369 := by
  unfold tailWord_79105
  simp only [CollatzResearch.WordTrace]
  refine ⟨2885196378423569903518769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1923464252282379935679179 2885196378423569903518769)
  ·
    refine ⟨2163897283817677427639077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2885196378423569903518769 2163897283817677427639077)
    ·
      refine ⟨405730740715814517682327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2163897283817677427639077 405730740715814517682327)
      ·
        refine ⟨608596111073721776523491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 405730740715814517682327 608596111073721776523491)
        ·
          refine ⟨912894166610582664785237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 608596111073721776523491 912894166610582664785237)
          ·
            refine ⟨1337247314370970700369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 912894166610582664785237 1337247314370970700369)
            ·
              rfl

theorem cell20_79105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 11].length) (baseStart_79105 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79105 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79105 prefixEnd_79105 := by exact prefixLift 79105
  have htrace : WordTrace (prefixWord ++ tailWord_79105) baseStart_79105 baseEnd_79105 := by
    simpa [prefixWord, tailWord_79105, baseEnd_79105] using wordTrace_append hprefix tailTrace_79105
  have hstable : (prefixWord ++ tailWord_79105).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79105).length < 2 ^ (prefixWord ++ tailWord_79105).sum := by decide
  have hdescent : baseEnd_79105 < baseStart_79105 := by decide
  rcases family_descends (prefixWord ++ tailWord_79105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79108 : List Nat := [2, 3, 2, 2, 2, 1, 1, 4, 3]
def baseStart_79108 : Nat := 118140960795 + 79108 * 2 ^ 59
def prefixEnd_79108 : Nat := 4983230072969 + 3 ^ 40 * 79108 * 2
def baseEnd_79108 : Nat := 36107046769761531809951

theorem tailTrace_79108 : CollatzResearch.WordTrace tailWord_79108 prefixEnd_79108 36107046769761531809951 := by
  unfold tailWord_79108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1442652898706350707938989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1923537198275134277251985 1442652898706350707938989)
  ·
    refine ⟨540994837014881515477121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1442652898706350707938989 540994837014881515477121)
    ·
      refine ⟨405746127761161136607841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 540994837014881515477121 405746127761161136607841)
      ·
        refine ⟨304309595820870852455881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 405746127761161136607841 304309595820870852455881)
        ·
          refine ⟨228232196865653139341911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 304309595820870852455881 228232196865653139341911)
          ·
            refine ⟨342348295298479709012867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228232196865653139341911 342348295298479709012867)
            ·
              refine ⟨513522442947719563519301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342348295298479709012867 513522442947719563519301)
              ·
                refine ⟨96285458052697418159869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 513522442947719563519301 96285458052697418159869)
                ·
                  refine ⟨36107046769761531809951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96285458052697418159869 36107046769761531809951)
                  ·
                    rfl

theorem cell20_79108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 1, 1, 4, 3].length) (baseStart_79108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79108 prefixEnd_79108 := by exact prefixLift 79108
  have htrace : WordTrace (prefixWord ++ tailWord_79108) baseStart_79108 baseEnd_79108 := by
    simpa [prefixWord, tailWord_79108, baseEnd_79108] using wordTrace_append hprefix tailTrace_79108
  have hstable : (prefixWord ++ tailWord_79108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79108).length < 2 ^ (prefixWord ++ tailWord_79108).sum := by decide
  have hdescent : baseEnd_79108 < baseStart_79108 := by decide
  rcases family_descends (prefixWord ++ tailWord_79108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79149 : List Nat := [1, 5, 3, 1, 1, 1, 1, 5, 2]
def baseStart_79149 : Nat := 118140960795 + 79149 * 2 ^ 59
def prefixEnd_79149 : Nat := 4983230072969 + 3 ^ 40 * 79149 * 2
def baseEnd_79149 : Nat := 36125760286947611443117

theorem tailTrace_79149 : CollatzResearch.WordTrace tailWord_79149 prefixEnd_79149 36125760286947611443117 := by
  unfold tailWord_79149
  simp only [CollatzResearch.WordTrace]
  refine ⟨2886801190264165418120501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1924534126842776945413667 2886801190264165418120501)
  ·
    refine ⟨270637611587265507948797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2886801190264165418120501 270637611587265507948797)
    ·
      refine ⟨101489104345224565480799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 270637611587265507948797 101489104345224565480799)
      ·
        refine ⟨152233656517836848221199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101489104345224565480799 152233656517836848221199)
        ·
          refine ⟨228350484776755272331799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152233656517836848221199 228350484776755272331799)
          ·
            refine ⟨342525727165132908497699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 228350484776755272331799 342525727165132908497699)
            ·
              refine ⟨513788590747699362746549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 342525727165132908497699 513788590747699362746549)
              ·
                refine ⟨48167680382596815257489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 513788590747699362746549 48167680382596815257489)
                ·
                  refine ⟨36125760286947611443117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48167680382596815257489 36125760286947611443117)
                  ·
                    rfl

theorem cell20_79149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 1, 5, 2].length) (baseStart_79149 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79149 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79149 prefixEnd_79149 := by exact prefixLift 79149
  have htrace : WordTrace (prefixWord ++ tailWord_79149) baseStart_79149 baseEnd_79149 := by
    simpa [prefixWord, tailWord_79149, baseEnd_79149] using wordTrace_append hprefix tailTrace_79149
  have hstable : (prefixWord ++ tailWord_79149).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79149).length < 2 ^ (prefixWord ++ tailWord_79149).sum := by decide
  have hdescent : baseEnd_79149 < baseStart_79149 := by decide
  rcases family_descends (prefixWord ++ tailWord_79149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79167 : List Nat := [1, 1, 2, 2, 4, 3, 1, 1, 5]
def baseStart_79167 : Nat := 118140960795 + 79167 * 2 ^ 59
def prefixEnd_79167 : Nat := 4983230072969 + 3 ^ 40 * 79167 * 2
def baseEnd_79167 : Nat := 36133975977419548843043

theorem tailTrace_79167 : CollatzResearch.WordTrace tailWord_79167 prefixEnd_79167 36133975977419548843043 := by
  unfold tailWord_79167
  simp only [CollatzResearch.WordTrace]
  refine ⟨2887457704198954492275755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1924971802799302994850503 2887457704198954492275755)
  ·
    refine ⟨4331186556298431738413633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2887457704198954492275755 4331186556298431738413633)
    ·
      refine ⟨3248389917223823803810225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4331186556298431738413633 3248389917223823803810225)
      ·
        refine ⟨2436292437917867852857669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3248389917223823803810225 2436292437917867852857669)
        ·
          refine ⟨456804832109600222410813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2436292437917867852857669 456804832109600222410813)
          ·
            refine ⟨171301812041100083404055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 456804832109600222410813 171301812041100083404055)
            ·
              refine ⟨256952718061650125106083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 171301812041100083404055 256952718061650125106083)
              ·
                refine ⟨385429077092475187659125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 256952718061650125106083 385429077092475187659125)
                ·
                  refine ⟨36133975977419548843043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 385429077092475187659125 36133975977419548843043)
                  ·
                    rfl

theorem cell20_79167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 1, 1, 5].length) (baseStart_79167 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79167 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79167 prefixEnd_79167 := by exact prefixLift 79167
  have htrace : WordTrace (prefixWord ++ tailWord_79167) baseStart_79167 baseEnd_79167 := by
    simpa [prefixWord, tailWord_79167, baseEnd_79167] using wordTrace_append hprefix tailTrace_79167
  have hstable : (prefixWord ++ tailWord_79167).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79167).length < 2 ^ (prefixWord ++ tailWord_79167).sum := by decide
  have hdescent : baseEnd_79167 < baseStart_79167 := by decide
  rcases family_descends (prefixWord ++ tailWord_79167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79184 : List Nat := [2, 1, 1, 1, 1, 5, 5, 1, 3]
def baseStart_79184 : Nat := 118140960795 + 79184 * 2 ^ 59
def prefixEnd_79184 : Nat := 4983230072969 + 3 ^ 40 * 79184 * 2
def baseEnd_79184 : Nat := 36141735240643045276307

theorem tailTrace_79184 : CollatzResearch.WordTrace tailWord_79184 prefixEnd_79184 36141735240643045276307 := by
  unfold tailWord_79184
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444038872568683197822303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1925385163424910930429737 1444038872568683197822303)
  ·
    refine ⟨2166058308853024796733455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1444038872568683197822303 2166058308853024796733455)
    ·
      refine ⟨3249087463279537195100183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2166058308853024796733455 3249087463279537195100183)
      ·
        refine ⟨4873631194919305792650275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3249087463279537195100183 4873631194919305792650275)
        ·
          refine ⟨7310446792378958688975413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4873631194919305792650275 7310446792378958688975413)
          ·
            refine ⟨685354386785527377091445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7310446792378958688975413 685354386785527377091445)
            ·
              refine ⟨64251973761143191602323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 685354386785527377091445 64251973761143191602323)
              ·
                refine ⟨96377960641714787403485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64251973761143191602323 96377960641714787403485)
                ·
                  refine ⟨36141735240643045276307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96377960641714787403485 36141735240643045276307)
                  ·
                    rfl

theorem cell20_79184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 5, 1, 3].length) (baseStart_79184 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79184 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79184 prefixEnd_79184 := by exact prefixLift 79184
  have htrace : WordTrace (prefixWord ++ tailWord_79184) baseStart_79184 baseEnd_79184 := by
    simpa [prefixWord, tailWord_79184, baseEnd_79184] using wordTrace_append hprefix tailTrace_79184
  have hstable : (prefixWord ++ tailWord_79184).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79184).length < 2 ^ (prefixWord ++ tailWord_79184).sum := by decide
  have hdescent : baseEnd_79184 < baseStart_79184 := by decide
  rcases family_descends (prefixWord ++ tailWord_79184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79236 : List Nat := [2, 3, 2, 1, 1, 4, 2, 5]
def baseStart_79236 : Nat := 118140960795 + 79236 * 2 ^ 59
def prefixEnd_79236 : Nat := 4983230072969 + 3 ^ 40 * 79236 * 2
def baseEnd_79236 : Nat := 12055156485853991847587

theorem tailTrace_79236 : CollatzResearch.WordTrace tailWord_79236 prefixEnd_79236 12055156485853991847587 := by
  unfold tailWord_79236
  simp only [CollatzResearch.WordTrace]
  refine ⟨1444987170474489638268781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1926649560632652851025041 1444987170474489638268781)
  ·
    refine ⟨541870188927933614350793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1444987170474489638268781 541870188927933614350793)
    ·
      refine ⟨406402641695950210763095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 541870188927933614350793 406402641695950210763095)
      ·
        refine ⟨609603962543925316144643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 406402641695950210763095 609603962543925316144643)
        ·
          refine ⟨914405943815887974216965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 609603962543925316144643 914405943815887974216965)
          ·
            refine ⟨171451114465478995165681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 914405943815887974216965 171451114465478995165681)
            ·
              refine ⟨128588335849109246374261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171451114465478995165681 128588335849109246374261)
              ·
                refine ⟨12055156485853991847587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128588335849109246374261 12055156485853991847587)
                ·
                  rfl

theorem cell20_79236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 2, 5].length) (baseStart_79236 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79236 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79236 prefixEnd_79236 := by exact prefixLift 79236
  have htrace : WordTrace (prefixWord ++ tailWord_79236) baseStart_79236 baseEnd_79236 := by
    simpa [prefixWord, tailWord_79236, baseEnd_79236] using wordTrace_append hprefix tailTrace_79236
  have hstable : (prefixWord ++ tailWord_79236).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79236).length < 2 ^ (prefixWord ++ tailWord_79236).sum := by decide
  have hdescent : baseEnd_79236 < baseStart_79236 := by decide
  rcases family_descends (prefixWord ++ tailWord_79236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79239 : List Nat := [1, 1, 4, 2, 2, 4, 2, 1, 3]
def baseStart_79239 : Nat := 118140960795 + 79239 * 2 ^ 59
def prefixEnd_79239 : Nat := 4983230072969 + 3 ^ 40 * 79239 * 2
def baseEnd_79239 : Nat := 36166838739307298442749

theorem tailTrace_79239 : CollatzResearch.WordTrace tailWord_79239 prefixEnd_79239 36166838739307298442749 := by
  unfold tailWord_79239
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890083759938110788896771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1926722506625407192597847 2890083759938110788896771)
  ·
    refine ⟨4335125639907166183345157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2890083759938110788896771 4335125639907166183345157)
    ·
      refine ⟨812836057482593659377217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4335125639907166183345157 812836057482593659377217)
      ·
        refine ⟨609627043111945244532913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 812836057482593659377217 609627043111945244532913)
        ·
          refine ⟨457220282333958933399685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 609627043111945244532913 457220282333958933399685)
          ·
            refine ⟨85728802937617300012441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 457220282333958933399685 85728802937617300012441)
            ·
              refine ⟨64296602203212975009331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85728802937617300012441 64296602203212975009331)
              ·
                refine ⟨96444903304819462513997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64296602203212975009331 96444903304819462513997)
                ·
                  refine ⟨36166838739307298442749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96444903304819462513997 36166838739307298442749)
                  ·
                    rfl

theorem cell20_79239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 2, 1, 3].length) (baseStart_79239 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79239 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79239 prefixEnd_79239 := by exact prefixLift 79239
  have htrace : WordTrace (prefixWord ++ tailWord_79239) baseStart_79239 baseEnd_79239 := by
    simpa [prefixWord, tailWord_79239, baseEnd_79239] using wordTrace_append hprefix tailTrace_79239
  have hstable : (prefixWord ++ tailWord_79239).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79239).length < 2 ^ (prefixWord ++ tailWord_79239).sum := by decide
  have hdescent : baseEnd_79239 < baseStart_79239 := by decide
  rcases family_descends (prefixWord ++ tailWord_79239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79243 : List Nat := [1, 1, 1, 1, 4, 3, 3, 3, 3]
def baseStart_79243 : Nat := 118140960795 + 79243 * 2 ^ 59
def prefixEnd_79243 : Nat := 4983230072969 + 3 ^ 40 * 79243 * 2
def baseEnd_79243 : Nat := 36168664448301062309399

theorem tailTrace_79243 : CollatzResearch.WordTrace tailWord_79243 prefixEnd_79243 36168664448301062309399 := by
  unfold tailWord_79243
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890229651923619472042383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1926819767949079648028255 2890229651923619472042383)
  ·
    refine ⟨4335344477885429208063575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2890229651923619472042383 4335344477885429208063575)
    ·
      refine ⟨6503016716828143812095363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4335344477885429208063575 6503016716828143812095363)
      ·
        refine ⟨9754525075242215718143045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6503016716828143812095363 9754525075242215718143045)
        ·
          refine ⟨1828973451607915447151821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9754525075242215718143045 1828973451607915447151821)
          ·
            refine ⟨685865044352968292681933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1828973451607915447151821 685865044352968292681933)
            ·
              refine ⟨257199391632363109755725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 685865044352968292681933 257199391632363109755725)
              ·
                refine ⟨96449771862136166158397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 257199391632363109755725 96449771862136166158397)
                ·
                  refine ⟨36168664448301062309399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96449771862136166158397 36168664448301062309399)
                  ·
                    rfl

theorem cell20_79243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 3, 3, 3].length) (baseStart_79243 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79243 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79243 prefixEnd_79243 := by exact prefixLift 79243
  have htrace : WordTrace (prefixWord ++ tailWord_79243) baseStart_79243 baseEnd_79243 := by
    simpa [prefixWord, tailWord_79243, baseEnd_79243] using wordTrace_append hprefix tailTrace_79243
  have hstable : (prefixWord ++ tailWord_79243).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79243).length < 2 ^ (prefixWord ++ tailWord_79243).sum := by decide
  have hdescent : baseEnd_79243 < baseStart_79243 := by decide
  rcases family_descends (prefixWord ++ tailWord_79243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79257 : List Nat := [1, 2, 1, 2, 1, 5, 2, 6]
def baseStart_79257 : Nat := 118140960795 + 79257 * 2 ^ 59
def prefixEnd_79257 : Nat := 4983230072969 + 3 ^ 40 * 79257 * 2
def baseEnd_79257 : Nat := 12058351476593078614225

theorem tailTrace_79257 : CollatzResearch.WordTrace tailWord_79257 prefixEnd_79257 12058351476593078614225 := by
  unfold tailWord_79257
  simp only [CollatzResearch.WordTrace]
  refine ⟨2890740273872899863052025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1927160182581933242034683 2890740273872899863052025)
  ·
    refine ⟨2168055205404674897289019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2890740273872899863052025 2168055205404674897289019)
    ·
      refine ⟨3252082808107012345933529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2168055205404674897289019 3252082808107012345933529)
      ·
        refine ⟨2439062106080259259450147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3252082808107012345933529 2439062106080259259450147)
        ·
          refine ⟨3658593159120388889175221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2439062106080259259450147 3658593159120388889175221)
          ·
            refine ⟨342993108667536458360177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3658593159120388889175221 342993108667536458360177)
            ·
              refine ⟨257244831500652343770133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 342993108667536458360177 257244831500652343770133)
              ·
                refine ⟨12058351476593078614225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 257244831500652343770133 12058351476593078614225)
                ·
                  rfl

theorem cell20_79257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 2, 6].length) (baseStart_79257 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79257 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79257 prefixEnd_79257 := by exact prefixLift 79257
  have htrace : WordTrace (prefixWord ++ tailWord_79257) baseStart_79257 baseEnd_79257 := by
    simpa [prefixWord, tailWord_79257, baseEnd_79257] using wordTrace_append hprefix tailTrace_79257
  have hstable : (prefixWord ++ tailWord_79257).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79257).length < 2 ^ (prefixWord ++ tailWord_79257).sum := by decide
  have hdescent : baseEnd_79257 < baseStart_79257 := by decide
  rcases family_descends (prefixWord ++ tailWord_79257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79267 : List Nat := [1, 1, 1, 4, 1, 3, 2, 5, 2]
def baseStart_79267 : Nat := 118140960795 + 79267 * 2 ^ 59
def prefixEnd_79267 : Nat := 4983230072969 + 3 ^ 40 * 79267 * 2
def baseEnd_79267 : Nat := 36179618702263645509301

theorem tailTrace_79267 : CollatzResearch.WordTrace tailWord_79267 prefixEnd_79267 36179618702263645509301 := by
  unfold tailWord_79267
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891105003836671570916055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1927403335891114380610703 2891105003836671570916055)
  ·
    refine ⟨4336657505755007356374083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2891105003836671570916055 4336657505755007356374083)
    ·
      refine ⟨6504986258632511034561125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4336657505755007356374083 6504986258632511034561125)
      ·
        refine ⟨1219684923493595818980211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6504986258632511034561125 1219684923493595818980211)
        ·
          refine ⟨1829527385240393728470317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1219684923493595818980211 1829527385240393728470317)
          ·
            refine ⟨686072769465147648176369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1829527385240393728470317 686072769465147648176369)
            ·
              refine ⟨514554577098860736132277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 686072769465147648176369 514554577098860736132277)
              ·
                refine ⟨48239491603018194012401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 514554577098860736132277 48239491603018194012401)
                ·
                  refine ⟨36179618702263645509301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48239491603018194012401 36179618702263645509301)
                  ·
                    rfl

theorem cell20_79267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 2, 5, 2].length) (baseStart_79267 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79267 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79267 prefixEnd_79267 := by exact prefixLift 79267
  have htrace : WordTrace (prefixWord ++ tailWord_79267) baseStart_79267 baseEnd_79267 := by
    simpa [prefixWord, tailWord_79267, baseEnd_79267] using wordTrace_append hprefix tailTrace_79267
  have hstable : (prefixWord ++ tailWord_79267).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79267).length < 2 ^ (prefixWord ++ tailWord_79267).sum := by decide
  have hdescent : baseEnd_79267 < baseStart_79267 := by decide
  rcases family_descends (prefixWord ++ tailWord_79267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79274 : List Nat := [3, 1, 6, 10]
def baseStart_79274 : Nat := 118140960795 + 79274 * 2 ^ 59
def prefixEnd_79274 : Nat := 4983230072969 + 3 ^ 40 * 79274 * 2
def baseEnd_79274 : Nat := 148900467872439227473

theorem tailTrace_79274 : CollatzResearch.WordTrace tailWord_79274 prefixEnd_79274 148900467872439227473 := by
  unfold tailWord_79274
  simp only [CollatzResearch.WordTrace]
  refine ⟨722840078702827941605219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1927573543207541177613917 722840078702827941605219)
  ·
    refine ⟨1084260118054241912407829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 722840078702827941605219 1084260118054241912407829)
    ·
      refine ⟨50824693033792589644117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 1084260118054241912407829 50824693033792589644117)
      ·
        refine ⟨148900467872439227473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 10 50824693033792589644117 148900467872439227473)
        ·
          rfl

theorem cell20_79274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 10].length) (baseStart_79274 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79274 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79274 prefixEnd_79274 := by exact prefixLift 79274
  have htrace : WordTrace (prefixWord ++ tailWord_79274) baseStart_79274 baseEnd_79274 := by
    simpa [prefixWord, tailWord_79274, baseEnd_79274] using wordTrace_append hprefix tailTrace_79274
  have hstable : (prefixWord ++ tailWord_79274).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79274).length < 2 ^ (prefixWord ++ tailWord_79274).sum := by decide
  have hdescent : baseEnd_79274 < baseStart_79274 := by decide
  rcases family_descends (prefixWord ++ tailWord_79274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79277 : List Nat := [1, 5, 2, 2, 1, 2, 2, 2, 3]
def baseStart_79277 : Nat := 118140960795 + 79277 * 2 ^ 59
def prefixEnd_79277 : Nat := 4983230072969 + 3 ^ 40 * 79277 * 2
def baseEnd_79277 : Nat := 36184182974748055175927

theorem tailTrace_79277 : CollatzResearch.WordTrace tailWord_79277 prefixEnd_79277 36184182974748055175927 := by
  unfold tailWord_79277
  simp only [CollatzResearch.WordTrace]
  refine ⟨2891469733800443278780085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1927646489200295519186723 2891469733800443278780085)
  ·
    refine ⟨271075287543791557385633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 2891469733800443278780085 271075287543791557385633)
    ·
      refine ⟨203306465657843668039225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 271075287543791557385633 203306465657843668039225)
      ·
        refine ⟨152479849243382751029419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 203306465657843668039225 152479849243382751029419)
        ·
          refine ⟨228719773865074126544129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152479849243382751029419 228719773865074126544129)
          ·
            refine ⟨171539830398805594908097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 228719773865074126544129 171539830398805594908097)
            ·
              refine ⟨128654872799104196181073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171539830398805594908097 128654872799104196181073)
              ·
                refine ⟨96491154599328147135805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 128654872799104196181073 96491154599328147135805)
                ·
                  refine ⟨36184182974748055175927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96491154599328147135805 36184182974748055175927)
                  ·
                    rfl

theorem cell20_79277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_79277 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79277 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79277 prefixEnd_79277 := by exact prefixLift 79277
  have htrace : WordTrace (prefixWord ++ tailWord_79277) baseStart_79277 baseEnd_79277 := by
    simpa [prefixWord, tailWord_79277, baseEnd_79277] using wordTrace_append hprefix tailTrace_79277
  have hstable : (prefixWord ++ tailWord_79277).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79277).length < 2 ^ (prefixWord ++ tailWord_79277).sum := by decide
  have hdescent : baseEnd_79277 < baseStart_79277 := by decide
  rcases family_descends (prefixWord ++ tailWord_79277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79322 : List Nat := [3, 1, 1, 2, 3, 3, 2, 3, 2]
def baseStart_79322 : Nat := 118140960795 + 79322 * 2 ^ 59
def prefixEnd_79322 : Nat := 4983230072969 + 3 ^ 40 * 79322 * 2
def baseEnd_79322 : Nat := 36204722200927898675743

theorem tailTrace_79322 : CollatzResearch.WordTrace tailWord_79322 prefixEnd_79322 36204722200927898675743 := by
  unfold tailWord_79322
  simp only [CollatzResearch.WordTrace]
  refine ⟨723277754659353991042055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1928740679091610642778813 723277754659353991042055)
  ·
    refine ⟨1084916631989030986563083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 723277754659353991042055 1084916631989030986563083)
    ·
      refine ⟨1627374947983546479844625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1084916631989030986563083 1627374947983546479844625)
      ·
        refine ⟨1220531210987659859883469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1627374947983546479844625 1220531210987659859883469)
        ·
          refine ⟨457699204120372447456301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1220531210987659859883469 457699204120372447456301)
          ·
            refine ⟨171637201545139667796113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 457699204120372447456301 171637201545139667796113)
            ·
              refine ⟨128727901158854750847085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 171637201545139667796113 128727901158854750847085)
              ·
                refine ⟨48272962934570531567657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128727901158854750847085 48272962934570531567657)
                ·
                  refine ⟨36204722200927898675743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48272962934570531567657 36204722200927898675743)
                  ·
                    rfl

theorem cell20_79322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 3, 2, 3, 2].length) (baseStart_79322 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79322 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79322 prefixEnd_79322 := by exact prefixLift 79322
  have htrace : WordTrace (prefixWord ++ tailWord_79322) baseStart_79322 baseEnd_79322 := by
    simpa [prefixWord, tailWord_79322, baseEnd_79322] using wordTrace_append hprefix tailTrace_79322
  have hstable : (prefixWord ++ tailWord_79322).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79322).length < 2 ^ (prefixWord ++ tailWord_79322).sum := by decide
  have hdescent : baseEnd_79322 < baseStart_79322 := by decide
  rcases family_descends (prefixWord ++ tailWord_79322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79343 : List Nat := [1, 1, 2, 1, 4, 1, 4, 4, 2]
def baseStart_79343 : Nat := 118140960795 + 79343 * 2 ^ 59
def prefixEnd_79343 : Nat := 4983230072969 + 3 ^ 40 * 79343 * 2
def baseEnd_79343 : Nat := 36214307173145158975657

theorem tailTrace_79343 : CollatzResearch.WordTrace tailWord_79343 prefixEnd_79343 36214307173145158975657 := by
  unfold tailWord_79343
  simp only [CollatzResearch.WordTrace]
  refine ⟨2893876951561336550682683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929251301040891033788455 2893876951561336550682683)
  ·
    refine ⟨4340815427342004826024025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2893876951561336550682683 4340815427342004826024025)
    ·
      refine ⟨3255611570506503619518019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4340815427342004826024025 3255611570506503619518019)
      ·
        refine ⟨4883417355759755429277029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3255611570506503619518019 4883417355759755429277029)
        ·
          refine ⟨915640754204954142989443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4883417355759755429277029 915640754204954142989443)
          ·
            refine ⟨1373461131307431214484165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 915640754204954142989443 1373461131307431214484165)
            ·
              refine ⟨257523962120143352715781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1373461131307431214484165 257523962120143352715781)
              ·
                refine ⟨48285742897526878634209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257523962120143352715781 48285742897526878634209)
                ·
                  refine ⟨36214307173145158975657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48285742897526878634209 36214307173145158975657)
                  ·
                    rfl

theorem cell20_79343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 4, 4, 2].length) (baseStart_79343 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79343 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79343 prefixEnd_79343 := by exact prefixLift 79343
  have htrace : WordTrace (prefixWord ++ tailWord_79343) baseStart_79343 baseEnd_79343 := by
    simpa [prefixWord, tailWord_79343, baseEnd_79343] using wordTrace_append hprefix tailTrace_79343
  have hstable : (prefixWord ++ tailWord_79343).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79343).length < 2 ^ (prefixWord ++ tailWord_79343).sum := by decide
  have hdescent : baseEnd_79343 < baseStart_79343 := by decide
  rcases family_descends (prefixWord ++ tailWord_79343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79367 : List Nat := [1, 1, 4, 3, 2, 3, 2, 4]
def baseStart_79367 : Nat := 118140960795 + 79367 * 2 ^ 59
def prefixEnd_79367 : Nat := 4983230072969 + 3 ^ 40 * 79367 * 2
def baseEnd_79367 : Nat := 12075087142369247391853

theorem tailTrace_79367 : CollatzResearch.WordTrace tailWord_79367 prefixEnd_79367 12075087142369247391853 := by
  unfold tailWord_79367
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894752303474388649556355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929834868982925766370903 2894752303474388649556355)
  ·
    refine ⟨4342128455211582974334533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2894752303474388649556355 4342128455211582974334533)
    ·
      refine ⟨814149085352171807687725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4342128455211582974334533 814149085352171807687725)
      ·
        refine ⟨305305907007064427882897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 814149085352171807687725 305305907007064427882897)
        ·
          refine ⟨228979430255298320912173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 305305907007064427882897 228979430255298320912173)
          ·
            refine ⟨85867286345736870342065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 228979430255298320912173 85867286345736870342065)
            ·
              refine ⟨64400464759302652756549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 85867286345736870342065 64400464759302652756549)
              ·
                refine ⟨12075087142369247391853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64400464759302652756549 12075087142369247391853)
                ·
                  rfl

theorem cell20_79367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 3, 2, 4].length) (baseStart_79367 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79367 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79367 prefixEnd_79367 := by exact prefixLift 79367
  have htrace : WordTrace (prefixWord ++ tailWord_79367) baseStart_79367 baseEnd_79367 := by
    simpa [prefixWord, tailWord_79367, baseEnd_79367] using wordTrace_append hprefix tailTrace_79367
  have hstable : (prefixWord ++ tailWord_79367).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79367).length < 2 ^ (prefixWord ++ tailWord_79367).sum := by decide
  have hdescent : baseEnd_79367 < baseStart_79367 := by decide
  rcases family_descends (prefixWord ++ tailWord_79367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79373 : List Nat := [1, 7, 1, 1, 2, 2, 1, 3, 2]
def baseStart_79373 : Nat := 118140960795 + 79373 * 2 ^ 59
def prefixEnd_79373 : Nat := 4983230072969 + 3 ^ 40 * 79373 * 2
def baseEnd_79373 : Nat := 36227999990598387975535

theorem tailTrace_79373 : CollatzResearch.WordTrace tailWord_79373 prefixEnd_79373 36227999990598387975535 := by
  unfold tailWord_79373
  simp only [CollatzResearch.WordTrace]
  refine ⟨2894971141452651674274773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1929980760968434449516515 2894971141452651674274773)
  ·
    refine ⟨67850886127796523615815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 2894971141452651674274773 67850886127796523615815)
    ·
      refine ⟨101776329191694785423723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67850886127796523615815 101776329191694785423723)
      ·
        refine ⟨152664493787542178135585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 101776329191694785423723 152664493787542178135585)
        ·
          refine ⟨114498370340656633601689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 152664493787542178135585 114498370340656633601689)
          ·
            refine ⟨85873777755492475201267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 114498370340656633601689 85873777755492475201267)
            ·
              refine ⟨128810666633238712801901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85873777755492475201267 128810666633238712801901)
              ·
                refine ⟨48303999987464517300713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 128810666633238712801901 48303999987464517300713)
                ·
                  refine ⟨36227999990598387975535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48303999987464517300713 36227999990598387975535)
                  ·
                    rfl

theorem cell20_79373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_79373 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79373 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79373 prefixEnd_79373 := by exact prefixLift 79373
  have htrace : WordTrace (prefixWord ++ tailWord_79373) baseStart_79373 baseEnd_79373 := by
    simpa [prefixWord, tailWord_79373, baseEnd_79373] using wordTrace_append hprefix tailTrace_79373
  have hstable : (prefixWord ++ tailWord_79373).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79373).length < 2 ^ (prefixWord ++ tailWord_79373).sum := by decide
  have hdescent : baseEnd_79373 < baseStart_79373 := by decide
  rcases family_descends (prefixWord ++ tailWord_79373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79390 : List Nat := [4, 3, 3, 1, 1, 1, 3, 2, 2]
def baseStart_79390 : Nat := 118140960795 + 79390 * 2 ^ 59
def prefixEnd_79390 : Nat := 4983230072969 + 3 ^ 40 * 79390 * 2
def baseEnd_79390 : Nat := 36235759253821884408799

theorem tailTrace_79390 : CollatzResearch.WordTrace tailWord_79390 prefixEnd_79390 36235759253821884408799 := by
  unfold tailWord_79390
  simp only [CollatzResearch.WordTrace]
  refine ⟨361948897798882947205453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1930394121594042385095749 361948897798882947205453)
  ·
    refine ⟨135730836674581105202045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 361948897798882947205453 135730836674581105202045)
    ·
      refine ⟨50899063752967914450767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 135730836674581105202045 50899063752967914450767)
      ·
        refine ⟨76348595629451871676151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50899063752967914450767 76348595629451871676151)
        ·
          refine ⟨114522893444177807514227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76348595629451871676151 114522893444177807514227)
          ·
            refine ⟨171784340166266711271341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114522893444177807514227 171784340166266711271341)
            ·
              refine ⟨64419127562350016726753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 171784340166266711271341 64419127562350016726753)
              ·
                refine ⟨48314345671762512545065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64419127562350016726753 48314345671762512545065)
                ·
                  refine ⟨36235759253821884408799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48314345671762512545065 36235759253821884408799)
                  ·
                    rfl

theorem cell20_79390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_79390 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79390 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79390 prefixEnd_79390 := by exact prefixLift 79390
  have htrace : WordTrace (prefixWord ++ tailWord_79390) baseStart_79390 baseEnd_79390 := by
    simpa [prefixWord, tailWord_79390, baseEnd_79390] using wordTrace_append hprefix tailTrace_79390
  have hstable : (prefixWord ++ tailWord_79390).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79390).length < 2 ^ (prefixWord ++ tailWord_79390).sum := by decide
  have hdescent : baseEnd_79390 < baseStart_79390 := by decide
  rcases family_descends (prefixWord ++ tailWord_79390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79457 : List Nat := [1, 2, 3, 1, 1, 3, 3, 4, 2]
def baseStart_79457 : Nat := 118140960795 + 79457 * 2 ^ 59
def prefixEnd_79457 : Nat := 4983230072969 + 3 ^ 40 * 79457 * 2
def baseEnd_79457 : Nat := 36266339879467429175191

theorem tailTrace_79457 : CollatzResearch.WordTrace tailWord_79457 prefixEnd_79457 36266339879467429175191 := by
  unfold tailWord_79457
  simp only [CollatzResearch.WordTrace]
  refine ⟨2898034873148334020332625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1932023248765556013555083 2898034873148334020332625)
  ·
    refine ⟨2173526154861250515249469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2898034873148334020332625 2173526154861250515249469)
    ·
      refine ⟨815072308072968943218551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2173526154861250515249469 815072308072968943218551)
      ·
        refine ⟨1222608462109453414827827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 815072308072968943218551 1222608462109453414827827)
        ·
          refine ⟨1833912693164180122241741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1222608462109453414827827 1833912693164180122241741)
          ·
            refine ⟨687717259936567545840653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1833912693164180122241741 687717259936567545840653)
            ·
              refine ⟨257893972476212829690245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 687717259936567545840653 257893972476212829690245)
              ·
                refine ⟨48355119839289905566921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 257893972476212829690245 48355119839289905566921)
                ·
                  refine ⟨36266339879467429175191, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48355119839289905566921 36266339879467429175191)
                  ·
                    rfl

theorem cell20_79457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 3, 4, 2].length) (baseStart_79457 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79457 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79457 prefixEnd_79457 := by exact prefixLift 79457
  have htrace : WordTrace (prefixWord ++ tailWord_79457) baseStart_79457 baseEnd_79457 := by
    simpa [prefixWord, tailWord_79457, baseEnd_79457] using wordTrace_append hprefix tailTrace_79457
  have hstable : (prefixWord ++ tailWord_79457).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79457).length < 2 ^ (prefixWord ++ tailWord_79457).sum := by decide
  have hdescent : baseEnd_79457 < baseStart_79457 := by decide
  rcases family_descends (prefixWord ++ tailWord_79457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79464 : List Nat := [2, 1, 4, 3, 1, 1, 3, 5]
def baseStart_79464 : Nat := 118140960795 + 79464 * 2 ^ 59
def prefixEnd_79464 : Nat := 4983230072969 + 3 ^ 40 * 79464 * 2
def baseEnd_79464 : Nat := 12089844956735505313943

theorem tailTrace_79464 : CollatzResearch.WordTrace tailWord_79464 prefixEnd_79464 12089844956735505313943 := by
  unfold tailWord_79464
  simp only [CollatzResearch.WordTrace]
  refine ⟨1449145092061487107918723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1932193456081982810558297 1449145092061487107918723)
  ·
    refine ⟨2173717638092230661878085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1449145092061487107918723 2173717638092230661878085)
    ·
      refine ⟨407572057142293249102141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2173717638092230661878085 407572057142293249102141)
      ·
        refine ⟨152839521428359968413303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 407572057142293249102141 152839521428359968413303)
        ·
          refine ⟨229259282142539952619955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 152839521428359968413303 229259282142539952619955)
          ·
            refine ⟨343888923213809928929933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229259282142539952619955 343888923213809928929933)
            ·
              refine ⟨128958346205178723348725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 343888923213809928929933 128958346205178723348725)
              ·
                refine ⟨12089844956735505313943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 128958346205178723348725 12089844956735505313943)
                ·
                  rfl

theorem cell20_79464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 3, 5].length) (baseStart_79464 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79464 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79464 prefixEnd_79464 := by exact prefixLift 79464
  have htrace : WordTrace (prefixWord ++ tailWord_79464) baseStart_79464 baseEnd_79464 := by
    simpa [prefixWord, tailWord_79464, baseEnd_79464] using wordTrace_append hprefix tailTrace_79464
  have hstable : (prefixWord ++ tailWord_79464).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79464).length < 2 ^ (prefixWord ++ tailWord_79464).sum := by decide
  have hdescent : baseEnd_79464 < baseStart_79464 := by decide
  rcases family_descends (prefixWord ++ tailWord_79464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79495 : List Nat := [1, 1, 4, 2, 1, 3, 1, 5, 2]
def baseStart_79495 : Nat := 118140960795 + 79495 * 2 ^ 59
def prefixEnd_79495 : Nat := 4983230072969 + 3 ^ 40 * 79495 * 2
def baseEnd_79495 : Nat := 36283684114908185908369

theorem tailTrace_79495 : CollatzResearch.WordTrace tailWord_79495 prefixEnd_79495 36283684114908185908369 := by
  unfold tailWord_79495
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899420847010666510215939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1932947231340444340143959 2899420847010666510215939)
  ·
    refine ⟨4349131270515999765323909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899420847010666510215939 4349131270515999765323909)
    ·
      refine ⟨815462113221749955998233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4349131270515999765323909 815462113221749955998233)
      ·
        refine ⟨611596584916312466998675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 815462113221749955998233 611596584916312466998675)
        ·
          refine ⟨917394877374468700498013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 611596584916312466998675 917394877374468700498013)
          ·
            refine ⟨344023079015425762686755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 917394877374468700498013 344023079015425762686755)
            ·
              refine ⟨516034618523138644030133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 344023079015425762686755 516034618523138644030133)
              ·
                refine ⟨48378245486544247877825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 516034618523138644030133 48378245486544247877825)
                ·
                  refine ⟨36283684114908185908369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48378245486544247877825 36283684114908185908369)
                  ·
                    rfl

theorem cell20_79495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 5, 2].length) (baseStart_79495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79495 prefixEnd_79495 := by exact prefixLift 79495
  have htrace : WordTrace (prefixWord ++ tailWord_79495) baseStart_79495 baseEnd_79495 := by
    simpa [prefixWord, tailWord_79495, baseEnd_79495] using wordTrace_append hprefix tailTrace_79495
  have hstable : (prefixWord ++ tailWord_79495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79495).length < 2 ^ (prefixWord ++ tailWord_79495).sum := by decide
  have hdescent : baseEnd_79495 < baseStart_79495 := by decide
  rcases family_descends (prefixWord ++ tailWord_79495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79499 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 6]
def baseStart_79499 : Nat := 118140960795 + 79499 * 2 ^ 59
def prefixEnd_79499 : Nat := 4983230072969 + 3 ^ 40 * 79499 * 2
def baseEnd_79499 : Nat := 36285509823901949775019

theorem tailTrace_79499 : CollatzResearch.WordTrace tailWord_79499 prefixEnd_79499 36285509823901949775019 := by
  unfold tailWord_79499
  simp only [CollatzResearch.WordTrace]
  refine ⟨2899566738996175193361551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1933044492664116795574367 2899566738996175193361551)
  ·
    refine ⟨4349350108494262790042327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2899566738996175193361551 4349350108494262790042327)
    ·
      refine ⟨6524025162741394185063491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4349350108494262790042327 6524025162741394185063491)
      ·
        refine ⟨9786037744112091277595237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6524025162741394185063491 9786037744112091277595237)
        ·
          refine ⟨1834882077021017114549107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9786037744112091277595237 1834882077021017114549107)
          ·
            refine ⟨2752323115531525671823661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1834882077021017114549107 2752323115531525671823661)
            ·
              refine ⟨1032121168324322126933873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2752323115531525671823661 1032121168324322126933873)
              ·
                refine ⟨774090876243241595200405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1032121168324322126933873 774090876243241595200405)
                ·
                  refine ⟨36285509823901949775019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 774090876243241595200405 36285509823901949775019)
                  ·
                    rfl

theorem cell20_79499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 6].length) (baseStart_79499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79499 prefixEnd_79499 := by exact prefixLift 79499
  have htrace : WordTrace (prefixWord ++ tailWord_79499) baseStart_79499 baseEnd_79499 := by
    simpa [prefixWord, tailWord_79499, baseEnd_79499] using wordTrace_append hprefix tailTrace_79499
  have hstable : (prefixWord ++ tailWord_79499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79499).length < 2 ^ (prefixWord ++ tailWord_79499).sum := by decide
  have hdescent : baseEnd_79499 < baseStart_79499 := by decide
  rcases family_descends (prefixWord ++ tailWord_79499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79522 : List Nat := [3, 3, 1, 4, 1, 1, 3, 1, 3]
def baseStart_79522 : Nat := 118140960795 + 79522 * 2 ^ 59
def prefixEnd_79522 : Nat := 4983230072969 + 3 ^ 40 * 79522 * 2
def baseEnd_79522 : Nat := 36296007650616092008259

theorem tailTrace_79522 : CollatzResearch.WordTrace tailWord_79522 prefixEnd_79522 36296007650616092008259 := by
  unfold tailWord_79522
  simp only [CollatzResearch.WordTrace]
  refine ⟨725101404478212530362205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1933603745275233414299213 725101404478212530362205)
  ·
    refine ⟨271913026679329698885827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 725101404478212530362205 271913026679329698885827)
    ·
      refine ⟨407869540018994548328741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 271913026679329698885827 407869540018994548328741)
      ·
        refine ⟨76475538753561477811639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 407869540018994548328741 76475538753561477811639)
        ·
          refine ⟨114713308130342216717459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76475538753561477811639 114713308130342216717459)
          ·
            refine ⟨172069962195513325076189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114713308130342216717459 172069962195513325076189)
            ·
              refine ⟨64526235823317496903571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 172069962195513325076189 64526235823317496903571)
              ·
                refine ⟨96789353734976245355357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64526235823317496903571 96789353734976245355357)
                ·
                  refine ⟨36296007650616092008259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96789353734976245355357 36296007650616092008259)
                  ·
                    rfl

theorem cell20_79522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 3, 1, 3].length) (baseStart_79522 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79522 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79522 prefixEnd_79522 := by exact prefixLift 79522
  have htrace : WordTrace (prefixWord ++ tailWord_79522) baseStart_79522 baseEnd_79522 := by
    simpa [prefixWord, tailWord_79522, baseEnd_79522] using wordTrace_append hprefix tailTrace_79522
  have hstable : (prefixWord ++ tailWord_79522).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79522).length < 2 ^ (prefixWord ++ tailWord_79522).sum := by decide
  have hdescent : baseEnd_79522 < baseStart_79522 := by decide
  rcases family_descends (prefixWord ++ tailWord_79522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79550 : List Nat := [4, 2, 1, 1, 2, 2, 3, 3, 2]
def baseStart_79550 : Nat := 118140960795 + 79550 * 2 ^ 59
def prefixEnd_79550 : Nat := 4983230072969 + 3 ^ 40 * 79550 * 2
def baseEnd_79550 : Nat := 36308787613572439074811

theorem tailTrace_79550 : CollatzResearch.WordTrace tailWord_79550 prefixEnd_79550 36308787613572439074811 := by
  unfold tailWord_79550
  simp only [CollatzResearch.WordTrace]
  refine ⟨362678357726426362933513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1934284574540940602312069 362678357726426362933513)
  ·
    refine ⟨272008768294819772200135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 362678357726426362933513 272008768294819772200135)
    ·
      refine ⟨408013152442229658300203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272008768294819772200135 408013152442229658300203)
      ·
        refine ⟨612019728663344487450305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 408013152442229658300203 612019728663344487450305)
        ·
          refine ⟨459014796497508365587729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 612019728663344487450305 459014796497508365587729)
          ·
            refine ⟨344261097373131274190797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 459014796497508365587729 344261097373131274190797)
            ·
              refine ⟨129097911514924227821549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344261097373131274190797 129097911514924227821549)
              ·
                refine ⟨48411716818096585433081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 129097911514924227821549 48411716818096585433081)
                ·
                  refine ⟨36308787613572439074811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48411716818096585433081 36308787613572439074811)
                  ·
                    rfl

theorem cell20_79550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 3, 2].length) (baseStart_79550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79550 prefixEnd_79550 := by exact prefixLift 79550
  have htrace : WordTrace (prefixWord ++ tailWord_79550) baseStart_79550 baseEnd_79550 := by
    simpa [prefixWord, tailWord_79550, baseEnd_79550] using wordTrace_append hprefix tailTrace_79550
  have hstable : (prefixWord ++ tailWord_79550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79550).length < 2 ^ (prefixWord ++ tailWord_79550).sum := by decide
  have hdescent : baseEnd_79550 < baseStart_79550 := by decide
  rcases family_descends (prefixWord ++ tailWord_79550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79574 : List Nat := [5, 2, 1, 3, 1, 1, 2, 5]
def baseStart_79574 : Nat := 118140960795 + 79574 * 2 ^ 59
def prefixEnd_79574 : Nat := 4983230072969 + 3 ^ 40 * 79574 * 2
def baseEnd_79574 : Nat := 12106580622511674091571

theorem tailTrace_79574 : CollatzResearch.WordTrace tailWord_79574 prefixEnd_79574 12106580622511674091571 := by
  unfold tailWord_79574
  simp only [CollatzResearch.WordTrace]
  refine ⟨181393888357778937646361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1934868142482975334894517 181393888357778937646361)
  ·
    refine ⟨136045416268334203234771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 181393888357778937646361 136045416268334203234771)
    ·
      refine ⟨204068124402501304852157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 136045416268334203234771 204068124402501304852157)
      ·
        refine ⟨76525546650937989319559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204068124402501304852157 76525546650937989319559)
        ·
          refine ⟨114788319976406983979339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76525546650937989319559 114788319976406983979339)
          ·
            refine ⟨172182479964610475969009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114788319976406983979339 172182479964610475969009)
            ·
              refine ⟨129136859973457856976757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172182479964610475969009 129136859973457856976757)
              ·
                refine ⟨12106580622511674091571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129136859973457856976757 12106580622511674091571)
                ·
                  rfl

theorem cell20_79574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_79574 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79574 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79574 prefixEnd_79574 := by exact prefixLift 79574
  have htrace : WordTrace (prefixWord ++ tailWord_79574) baseStart_79574 baseEnd_79574 := by
    simpa [prefixWord, tailWord_79574, baseEnd_79574] using wordTrace_append hprefix tailTrace_79574
  have hstable : (prefixWord ++ tailWord_79574).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79574).length < 2 ^ (prefixWord ++ tailWord_79574).sum := by decide
  have hdescent : baseEnd_79574 < baseStart_79574 := by decide
  rcases family_descends (prefixWord ++ tailWord_79574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79581 : List Nat := [1, 4, 3, 3, 1, 1, 1, 3, 3]
def baseStart_79581 : Nat := 118140960795 + 79581 * 2 ^ 59
def prefixEnd_79581 : Nat := 4983230072969 + 3 ^ 40 * 79581 * 2
def baseEnd_79581 : Nat := 36322936858274109041351

theorem tailTrace_79581 : CollatzResearch.WordTrace tailWord_79581 prefixEnd_79581 36322936858274109041351 := by
  unfold tailWord_79581
  simp only [CollatzResearch.WordTrace]
  refine ⟨2902557524699103197846597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1935038349799402131897731 2902557524699103197846597)
  ·
    refine ⟨544229535881081849596237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2902557524699103197846597 544229535881081849596237)
    ·
      refine ⟨204086075955405693598589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 544229535881081849596237 204086075955405693598589)
      ·
        refine ⟨76532278483277135099471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 204086075955405693598589 76532278483277135099471)
        ·
          refine ⟨114798417724915702649207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76532278483277135099471 114798417724915702649207)
          ·
            refine ⟨172197626587373553973811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 114798417724915702649207 172197626587373553973811)
            ·
              refine ⟨258296439881060330960717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172197626587373553973811 258296439881060330960717)
              ·
                refine ⟨96861164955397624110269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258296439881060330960717 96861164955397624110269)
                ·
                  refine ⟨36322936858274109041351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96861164955397624110269 36322936858274109041351)
                  ·
                    rfl

theorem cell20_79581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 1, 1, 1, 3, 3].length) (baseStart_79581 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79581 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79581 prefixEnd_79581 := by exact prefixLift 79581
  have htrace : WordTrace (prefixWord ++ tailWord_79581) baseStart_79581 baseEnd_79581 := by
    simpa [prefixWord, tailWord_79581, baseEnd_79581] using wordTrace_append hprefix tailTrace_79581
  have hstable : (prefixWord ++ tailWord_79581).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79581).length < 2 ^ (prefixWord ++ tailWord_79581).sum := by decide
  have hdescent : baseEnd_79581 < baseStart_79581 := by decide
  rcases family_descends (prefixWord ++ tailWord_79581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79613 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 8]
def baseStart_79613 : Nat := 118140960795 + 79613 * 2 ^ 59
def prefixEnd_79613 : Nat := 4983230072969 + 3 ^ 40 * 79613 * 2
def baseEnd_79613 : Nat := 36337542530224219974553

theorem tailTrace_79613 : CollatzResearch.WordTrace tailWord_79613 prefixEnd_79613 36337542530224219974553 := by
  unfold tailWord_79613
  simp only [CollatzResearch.WordTrace]
  refine ⟨2903724660583172663011493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1935816440388781775340995 2903724660583172663011493)
  ·
    refine ⟨544448373859344874314655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2903724660583172663011493 544448373859344874314655)
    ·
      refine ⟨816672560789017311471983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 544448373859344874314655 816672560789017311471983)
      ·
        refine ⟨1225008841183525967207975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816672560789017311471983 1225008841183525967207975)
        ·
          refine ⟨1837513261775288950811963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1225008841183525967207975 1837513261775288950811963)
          ·
            refine ⟨2756269892662933426217945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1837513261775288950811963 2756269892662933426217945)
            ·
              refine ⟨2067202419497200069663459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2756269892662933426217945 2067202419497200069663459)
              ·
                refine ⟨3100803629245800104495189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2067202419497200069663459 3100803629245800104495189)
                ·
                  refine ⟨36337542530224219974553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3100803629245800104495189 36337542530224219974553)
                  ·
                    rfl

theorem cell20_79613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 8].length) (baseStart_79613 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79613 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79613 prefixEnd_79613 := by exact prefixLift 79613
  have htrace : WordTrace (prefixWord ++ tailWord_79613) baseStart_79613 baseEnd_79613 := by
    simpa [prefixWord, tailWord_79613, baseEnd_79613] using wordTrace_append hprefix tailTrace_79613
  have hstable : (prefixWord ++ tailWord_79613).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79613).length < 2 ^ (prefixWord ++ tailWord_79613).sum := by decide
  have hdescent : baseEnd_79613 < baseStart_79613 := by decide
  rcases family_descends (prefixWord ++ tailWord_79613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79626 : List Nat := [3, 1, 2, 2, 1, 3, 4, 2, 2]
def baseStart_79626 : Nat := 118140960795 + 79626 * 2 ^ 59
def prefixEnd_79626 : Nat := 4983230072969 + 3 ^ 40 * 79626 * 2
def baseEnd_79626 : Nat := 36343476084453952541167

theorem tailTrace_79626 : CollatzResearch.WordTrace tailWord_79626 prefixEnd_79626 36343476084453952541167 := by
  unfold tailWord_79626
  simp only [CollatzResearch.WordTrace]
  refine ⟨726049702384018970808683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1936132539690717255489821 726049702384018970808683)
  ·
    refine ⟨1089074553576028456213025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 726049702384018970808683 1089074553576028456213025)
    ·
      refine ⟨816805915182021342159769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1089074553576028456213025 816805915182021342159769)
      ·
        refine ⟨612604436386516006619827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 816805915182021342159769 612604436386516006619827)
        ·
          refine ⟨918906654579774009929741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 612604436386516006619827 918906654579774009929741)
          ·
            refine ⟨344589995467415253723653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 918906654579774009929741 344589995467415253723653)
            ·
              refine ⟨64610624150140360073185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 344589995467415253723653 64610624150140360073185)
              ·
                refine ⟨48457968112605270054889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64610624150140360073185 48457968112605270054889)
                ·
                  refine ⟨36343476084453952541167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48457968112605270054889 36343476084453952541167)
                  ·
                    rfl

theorem cell20_79626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 4, 2, 2].length) (baseStart_79626 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79626 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79626 prefixEnd_79626 := by exact prefixLift 79626
  have htrace : WordTrace (prefixWord ++ tailWord_79626) baseStart_79626 baseEnd_79626 := by
    simpa [prefixWord, tailWord_79626, baseEnd_79626] using wordTrace_append hprefix tailTrace_79626
  have hstable : (prefixWord ++ tailWord_79626).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79626).length < 2 ^ (prefixWord ++ tailWord_79626).sum := by decide
  have hdescent : baseEnd_79626 < baseStart_79626 := by decide
  rcases family_descends (prefixWord ++ tailWord_79626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79637 : List Nat := [1, 3, 2, 1, 2, 3, 3, 5]
def baseStart_79637 : Nat := 118140960795 + 79637 * 2 ^ 59
def prefixEnd_79637 : Nat := 4983230072969 + 3 ^ 40 * 79637 * 2
def baseEnd_79637 : Nat := 12116165594728934391485

theorem tailTrace_79637 : CollatzResearch.WordTrace tailWord_79637 prefixEnd_79637 12116165594728934391485 := by
  unfold tailWord_79637
  simp only [CollatzResearch.WordTrace]
  refine ⟨2904600012496224761885165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1936400008330816507923443 2904600012496224761885165)
  ·
    refine ⟨1089225004686084285706937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2904600012496224761885165 1089225004686084285706937)
    ·
      refine ⟨816918753514563214280203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1089225004686084285706937 816918753514563214280203)
      ·
        refine ⟨1225378130271844821420305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 816918753514563214280203 1225378130271844821420305)
        ·
          refine ⟨919033597703883616065229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225378130271844821420305 919033597703883616065229)
          ·
            refine ⟨344637599138956356024461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 919033597703883616065229 344637599138956356024461)
            ·
              refine ⟨129239099677108633509173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344637599138956356024461 129239099677108633509173)
              ·
                refine ⟨12116165594728934391485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129239099677108633509173 12116165594728934391485)
                ·
                  rfl

theorem cell20_79637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 3, 5].length) (baseStart_79637 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79637 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79637 prefixEnd_79637 := by exact prefixLift 79637
  have htrace : WordTrace (prefixWord ++ tailWord_79637) baseStart_79637 baseEnd_79637 := by
    simpa [prefixWord, tailWord_79637, baseEnd_79637] using wordTrace_append hprefix tailTrace_79637
  have hstable : (prefixWord ++ tailWord_79637).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79637).length < 2 ^ (prefixWord ++ tailWord_79637).sum := by decide
  have hdescent : baseEnd_79637 < baseStart_79637 := by decide
  rcases family_descends (prefixWord ++ tailWord_79637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79651 : List Nat := [1, 1, 1, 4, 2, 1, 3, 1, 6]
def baseStart_79651 : Nat := 118140960795 + 79651 * 2 ^ 59
def prefixEnd_79651 : Nat := 4983230072969 + 3 ^ 40 * 79651 * 2
def baseEnd_79651 : Nat := 36354886765664976707731

theorem tailTrace_79651 : CollatzResearch.WordTrace tailWord_79651 prefixEnd_79651 36354886765664976707731 := by
  unfold tailWord_79651
  simp only [CollatzResearch.WordTrace]
  refine ⟨2905110634445505152894807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1936740422963670101929871 2905110634445505152894807)
  ·
    refine ⟨4357665951668257729342211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2905110634445505152894807 4357665951668257729342211)
    ·
      refine ⟨6536498927502386594013317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4357665951668257729342211 6536498927502386594013317)
      ·
        refine ⟨1225593548906697486377497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6536498927502386594013317 1225593548906697486377497)
        ·
          refine ⟨919195161680023114783123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1225593548906697486377497 919195161680023114783123)
          ·
            refine ⟨1378792742520034672174685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 919195161680023114783123 1378792742520034672174685)
            ·
              refine ⟨517047278445013002065507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1378792742520034672174685 517047278445013002065507)
              ·
                refine ⟨775570917667519503098261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517047278445013002065507 775570917667519503098261)
                ·
                  refine ⟨36354886765664976707731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 775570917667519503098261 36354886765664976707731)
                  ·
                    rfl

theorem cell20_79651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 1, 6].length) (baseStart_79651 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79651 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79651 prefixEnd_79651 := by exact prefixLift 79651
  have htrace : WordTrace (prefixWord ++ tailWord_79651) baseStart_79651 baseEnd_79651 := by
    simpa [prefixWord, tailWord_79651, baseEnd_79651] using wordTrace_append hprefix tailTrace_79651
  have hstable : (prefixWord ++ tailWord_79651).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79651).length < 2 ^ (prefixWord ++ tailWord_79651).sum := by decide
  have hdescent : baseEnd_79651 < baseStart_79651 := by decide
  rcases family_descends (prefixWord ++ tailWord_79651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79678 : List Nat := [4, 2, 1, 2, 2, 1, 3, 2, 3]
def baseStart_79678 : Nat := 118140960795 + 79678 * 2 ^ 59
def prefixEnd_79678 : Nat := 4983230072969 + 3 ^ 40 * 79678 * 2
def baseEnd_79678 : Nat := 36367210301372882807621

theorem tailTrace_79678 : CollatzResearch.WordTrace tailWord_79678 prefixEnd_79678 36367210301372882807621 := by
  unfold tailWord_79678
  simp only [CollatzResearch.WordTrace]
  refine ⟨363261925668461095515961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1937396936898459176085125 363261925668461095515961)
  ·
    refine ⟨272446444251345821636971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 363261925668461095515961 272446444251345821636971)
    ·
      refine ⟨408669666377018732455457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272446444251345821636971 408669666377018732455457)
      ·
        refine ⟨306502249782764049341593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408669666377018732455457 306502249782764049341593)
        ·
          refine ⟨229876687337073037006195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 306502249782764049341593 229876687337073037006195)
          ·
            refine ⟨344815031005609555509293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 229876687337073037006195 344815031005609555509293)
            ·
              refine ⟨129305636627103583315985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 344815031005609555509293 129305636627103583315985)
              ·
                refine ⟨96979227470327687486989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129305636627103583315985 96979227470327687486989)
                ·
                  refine ⟨36367210301372882807621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 96979227470327687486989 36367210301372882807621)
                  ·
                    rfl

theorem cell20_79678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_79678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79678 prefixEnd_79678 := by exact prefixLift 79678
  have htrace : WordTrace (prefixWord ++ tailWord_79678) baseStart_79678 baseEnd_79678 := by
    simpa [prefixWord, tailWord_79678, baseEnd_79678] using wordTrace_append hprefix tailTrace_79678
  have hstable : (prefixWord ++ tailWord_79678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79678).length < 2 ^ (prefixWord ++ tailWord_79678).sum := by decide
  have hdescent : baseEnd_79678 < baseStart_79678 := by decide
  rcases family_descends (prefixWord ++ tailWord_79678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79696 : List Nat := [2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_79696 : Nat := 118140960795 + 79696 * 2 ^ 59
def prefixEnd_79696 : Nat := 4983230072969 + 3 ^ 40 * 79696 * 2
def baseEnd_79696 : Nat := 12125141997281606735849

theorem tailTrace_79696 : CollatzResearch.WordTrace tailWord_79696 prefixEnd_79696 12125141997281606735849 := by
  unfold tailWord_79696
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453375959641238919141471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1937834612854985225521961 1453375959641238919141471)
  ·
    refine ⟨2180063939461858378712207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1453375959641238919141471 2180063939461858378712207)
    ·
      refine ⟨3270095909192787568068311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2180063939461858378712207 3270095909192787568068311)
      ·
        refine ⟨4905143863789181352102467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3270095909192787568068311 4905143863789181352102467)
        ·
          refine ⟨7357715795683772028153701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4905143863789181352102467 7357715795683772028153701)
          ·
            refine ⟨1379571711690707255278819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7357715795683772028153701 1379571711690707255278819)
            ·
              refine ⟨2069357567536060882918229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1379571711690707255278819 2069357567536060882918229)
              ·
                refine ⟨12125141997281606735849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2069357567536060882918229 12125141997281606735849)
                ·
                  rfl

theorem cell20_79696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_79696 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79696 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79696 prefixEnd_79696 := by exact prefixLift 79696
  have htrace : WordTrace (prefixWord ++ tailWord_79696) baseStart_79696 baseEnd_79696 := by
    simpa [prefixWord, tailWord_79696, baseEnd_79696] using wordTrace_append hprefix tailTrace_79696
  have hstable : (prefixWord ++ tailWord_79696).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79696).length < 2 ^ (prefixWord ++ tailWord_79696).sum := by decide
  have hdescent : baseEnd_79696 < baseStart_79696 := by decide
  rcases family_descends (prefixWord ++ tailWord_79696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79720 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 7]
def baseStart_79720 : Nat := 118140960795 + 79720 * 2 ^ 59
def prefixEnd_79720 : Nat := 4983230072969 + 3 ^ 40 * 79720 * 2
def baseEnd_79720 : Nat := 36386380245807403407449

theorem tailTrace_79720 : CollatzResearch.WordTrace tailWord_79720 prefixEnd_79720 36386380245807403407449 := by
  unfold tailWord_79720
  simp only [CollatzResearch.WordTrace]
  refine ⟨1453813635597764968578307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1938418180797019958104409 1453813635597764968578307)
  ·
    refine ⟨2180720453396647452867461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1453813635597764968578307 2180720453396647452867461)
    ·
      refine ⟨408885085011871397412649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2180720453396647452867461 408885085011871397412649)
      ·
        refine ⟨306663813758903548059487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 408885085011871397412649 306663813758903548059487)
        ·
          refine ⟨459995720638355322089231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 306663813758903548059487 459995720638355322089231)
          ·
            refine ⟨689993580957532983133847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 459995720638355322089231 689993580957532983133847)
            ·
              refine ⟨1034990371436299474700771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 689993580957532983133847 1034990371436299474700771)
              ·
                refine ⟨1552485557154449212051157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1034990371436299474700771 1552485557154449212051157)
                ·
                  refine ⟨36386380245807403407449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1552485557154449212051157 36386380245807403407449)
                  ·
                    rfl

theorem cell20_79720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 7].length) (baseStart_79720 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79720 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79720 prefixEnd_79720 := by exact prefixLift 79720
  have htrace : WordTrace (prefixWord ++ tailWord_79720) baseStart_79720 baseEnd_79720 := by
    simpa [prefixWord, tailWord_79720, baseEnd_79720] using wordTrace_append hprefix tailTrace_79720
  have hstable : (prefixWord ++ tailWord_79720).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79720).length < 2 ^ (prefixWord ++ tailWord_79720).sum := by decide
  have hdescent : baseEnd_79720 < baseStart_79720 := by decide
  rcases family_descends (prefixWord ++ tailWord_79720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79754 : List Nat := [3, 1, 2, 4, 2, 1, 1, 3, 3]
def baseStart_79754 : Nat := 118140960795 + 79754 * 2 ^ 59
def prefixEnd_79754 : Nat := 4983230072969 + 3 ^ 40 * 79754 * 2
def baseEnd_79754 : Nat := 36401898772254396273977

theorem tailTrace_79754 : CollatzResearch.WordTrace tailWord_79754 prefixEnd_79754 36401898772254396273977 := by
  unfold tailWord_79754
  simp only [CollatzResearch.WordTrace]
  refine ⟨727216838268088435973579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1939244902048235829262877 727216838268088435973579)
  ·
    refine ⟨1090825257402132653960369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 727216838268088435973579 1090825257402132653960369)
    ·
      refine ⟨818118943051599490470277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090825257402132653960369 818118943051599490470277)
      ·
        refine ⟨153397301822174904463177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 818118943051599490470277 153397301822174904463177)
        ·
          refine ⟨115047976366631178347383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153397301822174904463177 115047976366631178347383)
          ·
            refine ⟨172571964549946767521075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115047976366631178347383 172571964549946767521075)
            ·
              refine ⟨258857946824920151281613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172571964549946767521075 258857946824920151281613)
              ·
                refine ⟨97071730059345056730605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 258857946824920151281613 97071730059345056730605)
                ·
                  refine ⟨36401898772254396273977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97071730059345056730605 36401898772254396273977)
                  ·
                    rfl

theorem cell20_79754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 3, 3].length) (baseStart_79754 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79754 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79754 prefixEnd_79754 := by exact prefixLift 79754
  have htrace : WordTrace (prefixWord ++ tailWord_79754) baseStart_79754 baseEnd_79754 := by
    simpa [prefixWord, tailWord_79754, baseEnd_79754] using wordTrace_append hprefix tailTrace_79754
  have hstable : (prefixWord ++ tailWord_79754).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79754).length < 2 ^ (prefixWord ++ tailWord_79754).sum := by decide
  have hdescent : baseEnd_79754 < baseStart_79754 := by decide
  rcases family_descends (prefixWord ++ tailWord_79754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79765 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 6]
def baseStart_79765 : Nat := 118140960795 + 79765 * 2 ^ 59
def prefixEnd_79765 : Nat := 4983230072969 + 3 ^ 40 * 79765 * 2
def baseEnd_79765 : Nat := 36406919471987246907265

theorem tailTrace_79765 : CollatzResearch.WordTrace tailWord_79765 prefixEnd_79765 36406919471987246907265 := by
  unfold tailWord_79765
  simp only [CollatzResearch.WordTrace]
  refine ⟨2909268556032502622544749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1939512370688335081696499 2909268556032502622544749)
  ·
    refine ⟨1090975708512188483454281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2909268556032502622544749 1090975708512188483454281)
    ·
      refine ⟨818231781384141362590711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1090975708512188483454281 818231781384141362590711)
      ·
        refine ⟨1227347672076212043886067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 818231781384141362590711 1227347672076212043886067)
        ·
          refine ⟨1841021508114318065829101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1227347672076212043886067 1841021508114318065829101)
          ·
            refine ⟨690383065542869274685913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1841021508114318065829101 690383065542869274685913)
            ·
              refine ⟨517787299157151956014435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 690383065542869274685913 517787299157151956014435)
              ·
                refine ⟨776680948735727934021653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 517787299157151956014435 776680948735727934021653)
                ·
                  refine ⟨36406919471987246907265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 776680948735727934021653 36406919471987246907265)
                  ·
                    rfl

theorem cell20_79765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 6].length) (baseStart_79765 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79765 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79765 prefixEnd_79765 := by exact prefixLift 79765
  have htrace : WordTrace (prefixWord ++ tailWord_79765) baseStart_79765 baseEnd_79765 := by
    simpa [prefixWord, tailWord_79765, baseEnd_79765] using wordTrace_append hprefix tailTrace_79765
  have hstable : (prefixWord ++ tailWord_79765).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79765).length < 2 ^ (prefixWord ++ tailWord_79765).sum := by decide
  have hdescent : baseEnd_79765 < baseStart_79765 := by decide
  rcases family_descends (prefixWord ++ tailWord_79765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79806 : List Nat := [4, 2, 1, 1, 1, 5, 1, 5]
def baseStart_79806 : Nat := 118140960795 + 79806 * 2 ^ 59
def prefixEnd_79806 : Nat := 4983230072969 + 3 ^ 40 * 79806 * 2
def baseEnd_79806 : Nat := 12141877663057775513477

theorem tailTrace_79806 : CollatzResearch.WordTrace tailWord_79806 prefixEnd_79806 12141877663057775513477 := by
  unfold tailWord_79806
  simp only [CollatzResearch.WordTrace]
  refine ⟨363845493610495828098409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1940509299255977749858181 363845493610495828098409)
  ·
    refine ⟨272884120207871871073807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 363845493610495828098409 272884120207871871073807)
    ·
      refine ⟨409326180311807806610711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 272884120207871871073807 409326180311807806610711)
      ·
        refine ⟨613989270467711709916067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 409326180311807806610711 613989270467711709916067)
        ·
          refine ⟨920983905701567564874101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 613989270467711709916067 920983905701567564874101)
          ·
            refine ⟨86342241159521959206947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 920983905701567564874101 86342241159521959206947)
            ·
              refine ⟨129513361739282938810421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86342241159521959206947 129513361739282938810421)
              ·
                refine ⟨12141877663057775513477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 129513361739282938810421 12141877663057775513477)
                ·
                  rfl

theorem cell20_79806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 5, 1, 5].length) (baseStart_79806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79806 prefixEnd_79806 := by exact prefixLift 79806
  have htrace : WordTrace (prefixWord ++ tailWord_79806) baseStart_79806 baseEnd_79806 := by
    simpa [prefixWord, tailWord_79806, baseEnd_79806] using wordTrace_append hprefix tailTrace_79806
  have hstable : (prefixWord ++ tailWord_79806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79806).length < 2 ^ (prefixWord ++ tailWord_79806).sum := by decide
  have hdescent : baseEnd_79806 < baseStart_79806 := by decide
  rcases family_descends (prefixWord ++ tailWord_79806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79820 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 4]
def baseStart_79820 : Nat := 118140960795 + 79820 * 2 ^ 59
def prefixEnd_79820 : Nat := 4983230072969 + 3 ^ 40 * 79820 * 2
def baseEnd_79820 : Nat := 36432022970651500073707

theorem tailTrace_79820 : CollatzResearch.WordTrace tailWord_79820 prefixEnd_79820 36432022970651500073707 := by
  unfold tailWord_79820
  simp only [CollatzResearch.WordTrace]
  refine ⟨1455637285416623507898457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1940849713888831343864609 1455637285416623507898457)
  ·
    refine ⟨1091727964062467630923843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1455637285416623507898457 1091727964062467630923843)
    ·
      refine ⟨1637591946093701446385765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1091727964062467630923843 1637591946093701446385765)
      ·
        refine ⟨307048489892569021197331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1637591946093701446385765 307048489892569021197331)
        ·
          refine ⟨460572734838853531795997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 307048489892569021197331 460572734838853531795997)
          ·
            refine ⟨172714775564570074423499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 460572734838853531795997 172714775564570074423499)
            ·
              refine ⟨259072163346855111635249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172714775564570074423499 259072163346855111635249)
              ·
                refine ⟨194304122510141333726437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259072163346855111635249 194304122510141333726437)
                ·
                  refine ⟨36432022970651500073707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 194304122510141333726437 36432022970651500073707)
                  ·
                    rfl

theorem cell20_79820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 4].length) (baseStart_79820 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79820 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79820 prefixEnd_79820 := by exact prefixLift 79820
  have htrace : WordTrace (prefixWord ++ tailWord_79820) baseStart_79820 baseEnd_79820 := by
    simpa [prefixWord, tailWord_79820, baseEnd_79820] using wordTrace_append hprefix tailTrace_79820
  have hstable : (prefixWord ++ tailWord_79820).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79820).length < 2 ^ (prefixWord ++ tailWord_79820).sum := by decide
  have hdescent : baseEnd_79820 < baseStart_79820 := by decide
  rcases family_descends (prefixWord ++ tailWord_79820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79847 : List Nat := [1, 1, 5, 2, 4, 1, 1, 2, 3]
def baseStart_79847 : Nat := 118140960795 + 79847 * 2 ^ 59
def prefixEnd_79847 : Nat := 4983230072969 + 3 ^ 40 * 79847 * 2
def baseEnd_79847 : Nat := 36444346506359406173597

theorem tailTrace_79847 : CollatzResearch.WordTrace tailWord_79847 prefixEnd_79847 36444346506359406173597 := by
  unfold tailWord_79847
  simp only [CollatzResearch.WordTrace]
  refine ⟨2912259341735430627029795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1941506227823620418019863 2912259341735430627029795)
  ·
    refine ⟨4368389012603145940544693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2912259341735430627029795 4368389012603145940544693)
    ·
      refine ⟨409536469931544931926065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4368389012603145940544693 409536469931544931926065)
      ·
        refine ⟨307152352448658698944549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 409536469931544931926065 307152352448658698944549)
        ·
          refine ⟨57591066084123506052103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 307152352448658698944549 57591066084123506052103)
          ·
            refine ⟨86386599126185259078155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57591066084123506052103 86386599126185259078155)
            ·
              refine ⟨129579898689277888617233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86386599126185259078155 129579898689277888617233)
              ·
                refine ⟨97184924016958416462925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129579898689277888617233 97184924016958416462925)
                ·
                  refine ⟨36444346506359406173597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97184924016958416462925 36444346506359406173597)
                  ·
                    rfl

theorem cell20_79847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 4, 1, 1, 2, 3].length) (baseStart_79847 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79847 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79847 prefixEnd_79847 := by exact prefixLift 79847
  have htrace : WordTrace (prefixWord ++ tailWord_79847) baseStart_79847 baseEnd_79847 := by
    simpa [prefixWord, tailWord_79847, baseEnd_79847] using wordTrace_append hprefix tailTrace_79847
  have hstable : (prefixWord ++ tailWord_79847).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79847).length < 2 ^ (prefixWord ++ tailWord_79847).sum := by decide
  have hdescent : baseEnd_79847 < baseStart_79847 := by decide
  rcases family_descends (prefixWord ++ tailWord_79847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79927 : List Nat := [1, 1, 3, 1, 2, 2, 6, 1, 3]
def baseStart_79927 : Nat := 118140960795 + 79927 * 2 ^ 59
def prefixEnd_79927 : Nat := 4983230072969 + 3 ^ 40 * 79927 * 2
def baseEnd_79927 : Nat := 36480860686234683506603

theorem tailTrace_79927 : CollatzResearch.WordTrace tailWord_79927 prefixEnd_79927 36480860686234683506603 := by
  unfold tailWord_79927
  simp only [CollatzResearch.WordTrace]
  refine ⟨2915177181445604289942035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1943451454297069526628023 2915177181445604289942035)
  ·
    refine ⟨4372765772168406434913053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2915177181445604289942035 4372765772168406434913053)
    ·
      refine ⟨1639787164563152413092395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4372765772168406434913053 1639787164563152413092395)
      ·
        refine ⟨2459680746844728619638593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1639787164563152413092395 2459680746844728619638593)
        ·
          refine ⟨1844760560133546464728945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2459680746844728619638593 1844760560133546464728945)
          ·
            refine ⟨1383570420100159848546709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1844760560133546464728945 1383570420100159848546709)
            ·
              refine ⟨64854863442194992900627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1383570420100159848546709 64854863442194992900627)
              ·
                refine ⟨97282295163292489350941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64854863442194992900627 97282295163292489350941)
                ·
                  refine ⟨36480860686234683506603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97282295163292489350941 36480860686234683506603)
                  ·
                    rfl

theorem cell20_79927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 6, 1, 3].length) (baseStart_79927 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79927 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79927 prefixEnd_79927 := by exact prefixLift 79927
  have htrace : WordTrace (prefixWord ++ tailWord_79927) baseStart_79927 baseEnd_79927 := by
    simpa [prefixWord, tailWord_79927, baseEnd_79927] using wordTrace_append hprefix tailTrace_79927
  have hstable : (prefixWord ++ tailWord_79927).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79927).length < 2 ^ (prefixWord ++ tailWord_79927).sum := by decide
  have hdescent : baseEnd_79927 < baseStart_79927 := by decide
  rcases family_descends (prefixWord ++ tailWord_79927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79958 : List Nat := [5, 2, 2, 1, 1, 9]
def baseStart_79958 : Nat := 118140960795 + 79958 * 2 ^ 59
def prefixEnd_79958 : Nat := 4983230072969 + 3 ^ 40 * 79958 * 2
def baseEnd_79958 : Nat := 1351667034479124202709

theorem tailTrace_79958 : CollatzResearch.WordTrace tailWord_79958 prefixEnd_79958 1351667034479124202709 := by
  unfold tailWord_79958
  simp only [CollatzResearch.WordTrace]
  refine ⟨182269240270831036520033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1944205229555531056213685 182269240270831036520033)
  ·
    refine ⟨136701930203123277390025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 182269240270831036520033 136701930203123277390025)
    ·
      refine ⟨102526447652342458042519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 136701930203123277390025 102526447652342458042519)
      ·
        refine ⟨153789671478513687063779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102526447652342458042519 153789671478513687063779)
        ·
          refine ⟨230684507217770530595669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153789671478513687063779 230684507217770530595669)
          ·
            refine ⟨1351667034479124202709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 230684507217770530595669 1351667034479124202709)
            ·
              rfl

theorem cell20_79958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 9].length) (baseStart_79958 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79958 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79958 prefixEnd_79958 := by exact prefixLift 79958
  have htrace : WordTrace (prefixWord ++ tailWord_79958) baseStart_79958 baseEnd_79958 := by
    simpa [prefixWord, tailWord_79958, baseEnd_79958] using wordTrace_append hprefix tailTrace_79958
  have hstable : (prefixWord ++ tailWord_79958).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79958).length < 2 ^ (prefixWord ++ tailWord_79958).sum := by decide
  have hdescent : baseEnd_79958 < baseStart_79958 := by decide
  rcases family_descends (prefixWord ++ tailWord_79958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79968 : List Nat := [2, 1, 1, 3, 2, 5, 2, 2, 2]
def baseStart_79968 : Nat := 118140960795 + 79968 * 2 ^ 59
def prefixEnd_79968 : Nat := 4983230072969 + 3 ^ 40 * 79968 * 2
def baseEnd_79968 : Nat := 36499574203420763139769

theorem tailTrace_79968 : CollatzResearch.WordTrace tailWord_79968 prefixEnd_79968 36499574203420763139769 := by
  unfold tailWord_79968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1458336287148534146092279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1944448382864712194789705 1458336287148534146092279)
  ·
    refine ⟨2187504430722801219138419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1458336287148534146092279 2187504430722801219138419)
    ·
      refine ⟨3281256646084201828707629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2187504430722801219138419 3281256646084201828707629)
      ·
        refine ⟨1230471242281575685765361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3281256646084201828707629 1230471242281575685765361)
        ·
          refine ⟨922853431711181764324021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1230471242281575685765361 922853431711181764324021)
          ·
            refine ⟨86517509222923290405377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 922853431711181764324021 86517509222923290405377)
            ·
              refine ⟨64888131917192467804033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86517509222923290405377 64888131917192467804033)
              ·
                refine ⟨48666098937894350853025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64888131917192467804033 48666098937894350853025)
                ·
                  refine ⟨36499574203420763139769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48666098937894350853025 36499574203420763139769)
                  ·
                    rfl

theorem cell20_79968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 2, 2, 2].length) (baseStart_79968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79968 prefixEnd_79968 := by exact prefixLift 79968
  have htrace : WordTrace (prefixWord ++ tailWord_79968) baseStart_79968 baseEnd_79968 := by
    simpa [prefixWord, tailWord_79968, baseEnd_79968] using wordTrace_append hprefix tailTrace_79968
  have hstable : (prefixWord ++ tailWord_79968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79968).length < 2 ^ (prefixWord ++ tailWord_79968).sum := by decide
  have hdescent : baseEnd_79968 < baseStart_79968 := by decide
  rcases family_descends (prefixWord ++ tailWord_79968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_79993 : List Nat := [1, 2, 1, 3, 4, 1, 1, 1, 6]
def baseStart_79993 : Nat := 118140960795 + 79993 * 2 ^ 59
def prefixEnd_79993 : Nat := 4983230072969 + 3 ^ 40 * 79993 * 2
def baseEnd_79993 : Nat := 36510984884631787306333

theorem tailTrace_79993 : CollatzResearch.WordTrace tailWord_79993 prefixEnd_79993 36510984884631787306333 := by
  unfold tailWord_79993
  simp only [CollatzResearch.WordTrace]
  refine ⟨2917584399206497561844633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1945056266137665041229755 2917584399206497561844633)
  ·
    refine ⟨2188188299404873171383475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2917584399206497561844633 2188188299404873171383475)
    ·
      refine ⟨3282282449107309757075213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2188188299404873171383475 3282282449107309757075213)
      ·
        refine ⟨1230855918415241158903205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3282282449107309757075213 1230855918415241158903205)
        ·
          refine ⟨230785484702857717294351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1230855918415241158903205 230785484702857717294351)
          ·
            refine ⟨346178227054286575941527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230785484702857717294351 346178227054286575941527)
            ·
              refine ⟨519267340581429863912291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346178227054286575941527 519267340581429863912291)
              ·
                refine ⟨778901010872144795868437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519267340581429863912291 778901010872144795868437)
                ·
                  refine ⟨36510984884631787306333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 778901010872144795868437 36510984884631787306333)
                  ·
                    rfl

theorem cell20_79993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 1, 6].length) (baseStart_79993 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_79993 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_79993 prefixEnd_79993 := by exact prefixLift 79993
  have htrace : WordTrace (prefixWord ++ tailWord_79993) baseStart_79993 baseEnd_79993 := by
    simpa [prefixWord, tailWord_79993, baseEnd_79993] using wordTrace_append hprefix tailTrace_79993
  have hstable : (prefixWord ++ tailWord_79993).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_79993).length < 2 ^ (prefixWord ++ tailWord_79993).sum := by decide
  have hdescent : baseEnd_79993 < baseStart_79993 := by decide
  rcases family_descends (prefixWord ++ tailWord_79993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80020 : List Nat := [2, 4, 2, 3, 1, 1, 1, 1, 5]
def baseStart_80020 : Nat := 118140960795 + 80020 * 2 ^ 59
def prefixEnd_80020 : Nat := 4983230072969 + 3 ^ 40 * 80020 * 2
def baseEnd_80020 : Nat := 36523308420339693406223

theorem tailTrace_80020 : CollatzResearch.WordTrace tailWord_80020 prefixEnd_80020 36523308420339693406223 := by
  unfold tailWord_80020
  simp only [CollatzResearch.WordTrace]
  refine ⟨1459284585054340586538757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1945712780072454115385009 1459284585054340586538757)
  ·
    refine ⟨273615859697688859976017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1459284585054340586538757 273615859697688859976017)
    ·
      refine ⟨205211894773266644982013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 273615859697688859976017 205211894773266644982013)
      ·
        refine ⟨76954460539974991868255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205211894773266644982013 76954460539974991868255)
        ·
          refine ⟨115431690809962487802383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76954460539974991868255 115431690809962487802383)
          ·
            refine ⟨173147536214943731703575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115431690809962487802383 173147536214943731703575)
            ·
              refine ⟨259721304322415597555363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173147536214943731703575 259721304322415597555363)
              ·
                refine ⟨389581956483623396333045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 259721304322415597555363 389581956483623396333045)
                ·
                  refine ⟨36523308420339693406223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 389581956483623396333045 36523308420339693406223)
                  ·
                    rfl

theorem cell20_80020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 1, 1, 5].length) (baseStart_80020 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80020 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80020 prefixEnd_80020 := by exact prefixLift 80020
  have htrace : WordTrace (prefixWord ++ tailWord_80020) baseStart_80020 baseEnd_80020 := by
    simpa [prefixWord, tailWord_80020, baseEnd_80020] using wordTrace_append hprefix tailTrace_80020
  have hstable : (prefixWord ++ tailWord_80020).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80020).length < 2 ^ (prefixWord ++ tailWord_80020).sum := by decide
  have hdescent : baseEnd_80020 < baseStart_80020 := by decide
  rcases family_descends (prefixWord ++ tailWord_80020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80055 : List Nat := [1, 1, 3, 1, 4, 2, 4, 4]
def baseStart_80055 : Nat := 118140960795 + 80055 * 2 ^ 59
def prefixEnd_80055 : Nat := 4983230072969 + 3 ^ 40 * 80055 * 2
def baseEnd_80055 : Nat := 12179761124678375746471

theorem tailTrace_80055 : CollatzResearch.WordTrace tailWord_80055 prefixEnd_80055 12179761124678375746471 := by
  unfold tailWord_80055
  simp only [CollatzResearch.WordTrace]
  refine ⟨2919845724981882150601619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1946563816654588100401079 2919845724981882150601619)
  ·
    refine ⟨4379768587472823225902429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2919845724981882150601619 4379768587472823225902429)
    ·
      refine ⟨1642413220302308709713411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4379768587472823225902429 1642413220302308709713411)
      ·
        refine ⟨2463619830453463064570117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1642413220302308709713411 2463619830453463064570117)
        ·
          refine ⟨461928718210024324606897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2463619830453463064570117 461928718210024324606897)
          ·
            refine ⟨346446538657518243455173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 461928718210024324606897 346446538657518243455173)
            ·
              refine ⟨64958725998284670647845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 346446538657518243455173 64958725998284670647845)
              ·
                refine ⟨12179761124678375746471, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64958725998284670647845 12179761124678375746471)
                ·
                  rfl

theorem cell20_80055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 4, 4].length) (baseStart_80055 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80055 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80055 prefixEnd_80055 := by exact prefixLift 80055
  have htrace : WordTrace (prefixWord ++ tailWord_80055) baseStart_80055 baseEnd_80055 := by
    simpa [prefixWord, tailWord_80055, baseEnd_80055] using wordTrace_append hprefix tailTrace_80055
  have hstable : (prefixWord ++ tailWord_80055).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80055).length < 2 ^ (prefixWord ++ tailWord_80055).sum := by decide
  have hdescent : baseEnd_80055 < baseStart_80055 := by decide
  rcases family_descends (prefixWord ++ tailWord_80055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80082 : List Nat := [3, 2, 2, 2, 1, 3, 3, 2, 2]
def baseStart_80082 : Nat := 118140960795 + 80082 * 2 ^ 59
def prefixEnd_80082 : Nat := 4983230072969 + 3 ^ 40 * 80082 * 2
def baseEnd_80082 : Nat := 36551606909743033339303

theorem tailTrace_80082 : CollatzResearch.WordTrace tailWord_80082 prefixEnd_80082 36551606909743033339303 := by
  unfold tailWord_80082
  simp only [CollatzResearch.WordTrace]
  refine ⟨730207623971016440458625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1947220330589377174556333 730207623971016440458625)
  ·
    refine ⟨547655717978262330343969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 730207623971016440458625 547655717978262330343969)
    ·
      refine ⟨410741788483696747757977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 547655717978262330343969 410741788483696747757977)
      ·
        refine ⟨308056341362772560818483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 410741788483696747757977 308056341362772560818483)
        ·
          refine ⟨462084512044158841227725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308056341362772560818483 462084512044158841227725)
          ·
            refine ⟨173281692016559565460397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 462084512044158841227725 173281692016559565460397)
            ·
              refine ⟨64980634506209837047649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173281692016559565460397 64980634506209837047649)
              ·
                refine ⟨48735475879657377785737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 64980634506209837047649 48735475879657377785737)
                ·
                  refine ⟨36551606909743033339303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48735475879657377785737 36551606909743033339303)
                  ·
                    rfl

theorem cell20_80082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 3, 2, 2].length) (baseStart_80082 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80082 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80082 prefixEnd_80082 := by exact prefixLift 80082
  have htrace : WordTrace (prefixWord ++ tailWord_80082) baseStart_80082 baseEnd_80082 := by
    simpa [prefixWord, tailWord_80082, baseEnd_80082] using wordTrace_append hprefix tailTrace_80082
  have hstable : (prefixWord ++ tailWord_80082).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80082).length < 2 ^ (prefixWord ++ tailWord_80082).sum := by decide
  have hdescent : baseEnd_80082 < baseStart_80082 := by decide
  rcases family_descends (prefixWord ++ tailWord_80082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80092 : List Nat := [2, 2, 5, 2, 1, 2, 2, 1, 3]
def baseStart_80092 : Nat := 118140960795 + 80092 * 2 ^ 59
def prefixEnd_80092 : Nat := 4983230072969 + 3 ^ 40 * 80092 * 2
def baseEnd_80092 : Nat := 36556171182227443005929

theorem tailTrace_80092 : CollatzResearch.WordTrace tailWord_80092 prefixEnd_80092 36556171182227443005929 := by
  unfold tailWord_80092
  simp only [CollatzResearch.WordTrace]
  refine ⟨1460597612923918734849265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1947463483898558313132353 1460597612923918734849265)
  ·
    refine ⟨1095448209692939051136949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1460597612923918734849265 1095448209692939051136949)
    ·
      refine ⟨102698269658713036044089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1095448209692939051136949 102698269658713036044089)
      ·
        refine ⟨77023702244034777033067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102698269658713036044089 77023702244034777033067)
        ·
          refine ⟨115535553366052165549601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77023702244034777033067 115535553366052165549601)
          ·
            refine ⟨86651665024539124162201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115535553366052165549601 86651665024539124162201)
            ·
              refine ⟨64988748768404343121651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86651665024539124162201 64988748768404343121651)
              ·
                refine ⟨97483123152606514682477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64988748768404343121651 97483123152606514682477)
                ·
                  refine ⟨36556171182227443005929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97483123152606514682477 36556171182227443005929)
                  ·
                    rfl

theorem cell20_80092_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 2, 2, 1, 3].length) (baseStart_80092 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80092 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80092 prefixEnd_80092 := by exact prefixLift 80092
  have htrace : WordTrace (prefixWord ++ tailWord_80092) baseStart_80092 baseEnd_80092 := by
    simpa [prefixWord, tailWord_80092, baseEnd_80092] using wordTrace_append hprefix tailTrace_80092
  have hstable : (prefixWord ++ tailWord_80092).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80092).length < 2 ^ (prefixWord ++ tailWord_80092).sum := by decide
  have hdescent : baseEnd_80092 < baseStart_80092 := by decide
  rcases family_descends (prefixWord ++ tailWord_80092) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80093 : List Nat := [1, 4, 3, 2, 1, 1, 1, 7]
def baseStart_80093 : Nat := 118140960795 + 80093 * 2 ^ 59
def prefixEnd_80093 : Nat := 4983230072969 + 3 ^ 40 * 80093 * 2
def baseEnd_80093 : Nat := 12185542536491961324197

theorem tailTrace_80093 : CollatzResearch.WordTrace tailWord_80093 prefixEnd_80093 12185542536491961324197 := by
  unfold tailWord_80093
  simp only [CollatzResearch.WordTrace]
  refine ⟨2921231698844214640484933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1947487799229476426989955 2921231698844214640484933)
  ·
    refine ⟨547730943533290245090925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2921231698844214640484933 547730943533290245090925)
    ·
      refine ⟨205399103824983841909097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 547730943533290245090925 205399103824983841909097)
      ·
        refine ⟨154049327868737881431823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205399103824983841909097 154049327868737881431823)
        ·
          refine ⟨231073991803106822147735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154049327868737881431823 231073991803106822147735)
          ·
            refine ⟨346610987704660233221603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231073991803106822147735 346610987704660233221603)
            ·
              refine ⟨519916481556990349832405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346610987704660233221603 519916481556990349832405)
              ·
                refine ⟨12185542536491961324197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 519916481556990349832405 12185542536491961324197)
                ·
                  rfl

theorem cell20_80093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 1, 1, 7].length) (baseStart_80093 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80093 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80093 prefixEnd_80093 := by exact prefixLift 80093
  have htrace : WordTrace (prefixWord ++ tailWord_80093) baseStart_80093 baseEnd_80093 := by
    simpa [prefixWord, tailWord_80093, baseEnd_80093] using wordTrace_append hprefix tailTrace_80093
  have hstable : (prefixWord ++ tailWord_80093).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80093).length < 2 ^ (prefixWord ++ tailWord_80093).sum := by decide
  have hdescent : baseEnd_80093 < baseStart_80093 := by decide
  rcases family_descends (prefixWord ++ tailWord_80093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80121 : List Nat := [1, 2, 1, 3, 1, 1, 2, 4, 5]
def baseStart_80121 : Nat := 118140960795 + 80121 * 2 ^ 59
def prefixEnd_80121 : Nat := 4983230072969 + 3 ^ 40 * 80121 * 2
def baseEnd_80121 : Nat := 36569407572432231039143

theorem tailTrace_80121 : CollatzResearch.WordTrace tailWord_80121 prefixEnd_80121 36569407572432231039143 := by
  unfold tailWord_80121
  simp only [CollatzResearch.WordTrace]
  refine ⟨2922252942742775422504217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1948168628495183615002811 2922252942742775422504217)
  ·
    refine ⟨2191689707057081566878163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2922252942742775422504217 2191689707057081566878163)
    ·
      refine ⟨3287534560585622350317245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2191689707057081566878163 3287534560585622350317245)
      ·
        refine ⟨1232825460219608381368967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3287534560585622350317245 1232825460219608381368967)
        ·
          refine ⟨1849238190329412572053451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1232825460219608381368967 1849238190329412572053451)
          ·
            refine ⟨2773857285494118858080177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1849238190329412572053451 2773857285494118858080177)
            ·
              refine ⟨2080392964120589143560133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2773857285494118858080177 2080392964120589143560133)
              ·
                refine ⟨390073680772610464417525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2080392964120589143560133 390073680772610464417525)
                ·
                  refine ⟨36569407572432231039143, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390073680772610464417525 36569407572432231039143)
                  ·
                    rfl

theorem cell20_80121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 2, 4, 5].length) (baseStart_80121 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80121 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80121 prefixEnd_80121 := by exact prefixLift 80121
  have htrace : WordTrace (prefixWord ++ tailWord_80121) baseStart_80121 baseEnd_80121 := by
    simpa [prefixWord, tailWord_80121, baseEnd_80121] using wordTrace_append hprefix tailTrace_80121
  have hstable : (prefixWord ++ tailWord_80121).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80121).length < 2 ^ (prefixWord ++ tailWord_80121).sum := by decide
  have hdescent : baseEnd_80121 < baseStart_80121 := by decide
  rcases family_descends (prefixWord ++ tailWord_80121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80138 : List Nat := [3, 1, 2, 2, 1, 1, 3, 4, 3]
def baseStart_80138 : Nat := 118140960795 + 80138 * 2 ^ 59
def prefixEnd_80138 : Nat := 4983230072969 + 3 ^ 40 * 80138 * 2
def baseEnd_80138 : Nat := 36577166835655727472407

theorem tailTrace_80138 : CollatzResearch.WordTrace tailWord_80138 prefixEnd_80138 36577166835655727472407 := by
  unfold tailWord_80138
  simp only [CollatzResearch.WordTrace]
  refine ⟨730718245920296831468267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1948581989120791550582045 730718245920296831468267)
  ·
    refine ⟨1096077368880445247202401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 730718245920296831468267 1096077368880445247202401)
    ·
      refine ⟨822058026660333935401801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1096077368880445247202401 822058026660333935401801)
      ·
        refine ⟨616543519995250451551351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 822058026660333935401801 616543519995250451551351)
        ·
          refine ⟨924815279992875677327027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 616543519995250451551351 924815279992875677327027)
          ·
            refine ⟨1387222919989313515990541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 924815279992875677327027 1387222919989313515990541)
            ·
              refine ⟨520208594995992568496453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1387222919989313515990541 520208594995992568496453)
              ·
                refine ⟨97539111561748606593085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 520208594995992568496453 97539111561748606593085)
                ·
                  refine ⟨36577166835655727472407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97539111561748606593085 36577166835655727472407)
                  ·
                    rfl

theorem cell20_80138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 3, 4, 3].length) (baseStart_80138 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80138 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80138 prefixEnd_80138 := by exact prefixLift 80138
  have htrace : WordTrace (prefixWord ++ tailWord_80138) baseStart_80138 baseEnd_80138 := by
    simpa [prefixWord, tailWord_80138, baseEnd_80138] using wordTrace_append hprefix tailTrace_80138
  have hstable : (prefixWord ++ tailWord_80138).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80138).length < 2 ^ (prefixWord ++ tailWord_80138).sum := by decide
  have hdescent : baseEnd_80138 < baseStart_80138 := by decide
  rcases family_descends (prefixWord ++ tailWord_80138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80162 : List Nat := [3, 3, 1, 1, 3, 2, 1, 2, 4]
def baseStart_80162 : Nat := 118140960795 + 80162 * 2 ^ 59
def prefixEnd_80162 : Nat := 4983230072969 + 3 ^ 40 * 80162 * 2
def baseEnd_80162 : Nat := 36588121089618310672309

theorem tailTrace_80162 : CollatzResearch.WordTrace tailWord_80162 prefixEnd_80162 36588121089618310672309 := by
  unfold tailWord_80162
  simp only [CollatzResearch.WordTrace]
  refine ⟨730937083898559856186685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1949165557062826283164493 730937083898559856186685)
  ·
    refine ⟨274101406461959946070007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 730937083898559856186685 274101406461959946070007)
    ·
      refine ⟨411152109692939919105011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274101406461959946070007 411152109692939919105011)
      ·
        refine ⟨616728164539409878657517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411152109692939919105011 616728164539409878657517)
        ·
          refine ⟨231273061702278704496569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 616728164539409878657517 231273061702278704496569)
          ·
            refine ⟨173454796276709028372427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231273061702278704496569 173454796276709028372427)
            ·
              refine ⟨260182194415063542558641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173454796276709028372427 260182194415063542558641)
              ·
                refine ⟨195136645811297656918981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260182194415063542558641 195136645811297656918981)
                ·
                  refine ⟨36588121089618310672309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195136645811297656918981 36588121089618310672309)
                  ·
                    rfl

theorem cell20_80162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_80162 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80162 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80162 prefixEnd_80162 := by exact prefixLift 80162
  have htrace : WordTrace (prefixWord ++ tailWord_80162) baseStart_80162 baseEnd_80162 := by
    simpa [prefixWord, tailWord_80162, baseEnd_80162] using wordTrace_append hprefix tailTrace_80162
  have hstable : (prefixWord ++ tailWord_80162).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80162).length < 2 ^ (prefixWord ++ tailWord_80162).sum := by decide
  have hdescent : baseEnd_80162 < baseStart_80162 := by decide
  rcases family_descends (prefixWord ++ tailWord_80162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80193 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 5]
def baseStart_80193 : Nat := 118140960795 + 80193 * 2 ^ 59
def prefixEnd_80193 : Nat := 4983230072969 + 3 ^ 40 * 80193 * 2
def baseEnd_80193 : Nat := 36602270334319980638849

theorem tailTrace_80193 : CollatzResearch.WordTrace tailWord_80193 prefixEnd_80193 36602270334319980638849 := by
  unfold tailWord_80193
  simp only [CollatzResearch.WordTrace]
  refine ⟨2924878998481931719125233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1949919332321287812750155 2924878998481931719125233)
  ·
    refine ⟨2193659248861448789343925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2924878998481931719125233 2193659248861448789343925)
    ·
      refine ⟨205655554580760824000993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2193659248861448789343925 205655554580760824000993)
      ·
        refine ⟨154241665935570618000745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205655554580760824000993 154241665935570618000745)
        ·
          refine ⟨115681249451677963500559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154241665935570618000745 115681249451677963500559)
          ·
            refine ⟨173521874177516945250839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115681249451677963500559 173521874177516945250839)
            ·
              refine ⟨260282811266275417876259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173521874177516945250839 260282811266275417876259)
              ·
                refine ⟨390424216899413126814389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260282811266275417876259 390424216899413126814389)
                ·
                  refine ⟨36602270334319980638849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 390424216899413126814389 36602270334319980638849)
                  ·
                    rfl

theorem cell20_80193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 5].length) (baseStart_80193 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80193 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80193 prefixEnd_80193 := by exact prefixLift 80193
  have htrace : WordTrace (prefixWord ++ tailWord_80193) baseStart_80193 baseEnd_80193 := by
    simpa [prefixWord, tailWord_80193, baseEnd_80193] using wordTrace_append hprefix tailTrace_80193
  have hstable : (prefixWord ++ tailWord_80193).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80193).length < 2 ^ (prefixWord ++ tailWord_80193).sum := by decide
  have hdescent : baseEnd_80193 < baseStart_80193 := by decide
  rcases family_descends (prefixWord ++ tailWord_80193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80200 : List Nat := [2, 1, 3, 1, 1, 2, 4, 4, 2]
def baseStart_80200 : Nat := 118140960795 + 80200 * 2 ^ 59
def prefixEnd_80200 : Nat := 4983230072969 + 3 ^ 40 * 80200 * 2
def baseEnd_80200 : Nat := 36605465325059067405487

theorem tailTrace_80200 : CollatzResearch.WordTrace tailWord_80200 prefixEnd_80200 36605465325059067405487 := by
  unfold tailWord_80200
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462567154728285957315027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1950089539637714609753369 1462567154728285957315027)
  ·
    refine ⟨2193850732092428935972541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1462567154728285957315027 2193850732092428935972541)
    ·
      refine ⟨822694024534660850989703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2193850732092428935972541 822694024534660850989703)
      ·
        refine ⟨1234041036801991276484555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822694024534660850989703 1234041036801991276484555)
        ·
          refine ⟨1851061555202986914726833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1234041036801991276484555 1851061555202986914726833)
          ·
            refine ⟨1388296166402240186045125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1851061555202986914726833 1388296166402240186045125)
            ·
              refine ⟨260305531200420034883461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1388296166402240186045125 260305531200420034883461)
              ·
                refine ⟨48807287100078756540649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260305531200420034883461 48807287100078756540649)
                ·
                  refine ⟨36605465325059067405487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48807287100078756540649 36605465325059067405487)
                  ·
                    rfl

theorem cell20_80200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 4, 2].length) (baseStart_80200 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80200 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80200 prefixEnd_80200 := by exact prefixLift 80200
  have htrace : WordTrace (prefixWord ++ tailWord_80200) baseStart_80200 baseEnd_80200 := by
    simpa [prefixWord, tailWord_80200, baseEnd_80200] using wordTrace_append hprefix tailTrace_80200
  have hstable : (prefixWord ++ tailWord_80200).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80200).length < 2 ^ (prefixWord ++ tailWord_80200).sum := by decide
  have hdescent : baseEnd_80200 < baseStart_80200 := by decide
  rcases family_descends (prefixWord ++ tailWord_80200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80220 : List Nat := [2, 2, 4, 3, 2, 1, 2, 4]
def baseStart_80220 : Nat := 118140960795 + 80220 * 2 ^ 59
def prefixEnd_80220 : Nat := 4983230072969 + 3 ^ 40 * 80220 * 2
def baseEnd_80220 : Nat := 12204864623342628912913

theorem tailTrace_80220 : CollatzResearch.WordTrace tailWord_80220 prefixEnd_80220 12204864623342628912913 := by
  unfold tailWord_80220
  simp only [CollatzResearch.WordTrace]
  refine ⟨1462931884692057665179057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1950575846256076886905409 1462931884692057665179057)
  ·
    refine ⟨1097198913519043248884293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1462931884692057665179057 1097198913519043248884293)
    ·
      refine ⟨205724796284820609165805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1097198913519043248884293 205724796284820609165805)
      ·
        refine ⟨77146798606807728437177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205724796284820609165805 77146798606807728437177)
        ·
          refine ⟨57860098955105796327883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77146798606807728437177 57860098955105796327883)
          ·
            refine ⟨86790148432658694491825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57860098955105796327883 86790148432658694491825)
            ·
              refine ⟨65092611324494020868869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86790148432658694491825 65092611324494020868869)
              ·
                refine ⟨12204864623342628912913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65092611324494020868869 12204864623342628912913)
                ·
                  rfl

theorem cell20_80220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 3, 2, 1, 2, 4].length) (baseStart_80220 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80220 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80220 prefixEnd_80220 := by exact prefixLift 80220
  have htrace : WordTrace (prefixWord ++ tailWord_80220) baseStart_80220 baseEnd_80220 := by
    simpa [prefixWord, tailWord_80220, baseEnd_80220] using wordTrace_append hprefix tailTrace_80220
  have hstable : (prefixWord ++ tailWord_80220).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80220).length < 2 ^ (prefixWord ++ tailWord_80220).sum := by decide
  have hdescent : baseEnd_80220 < baseStart_80220 := by decide
  rcases family_descends (prefixWord ++ tailWord_80220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80224 : List Nat := [2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_80224 : Nat := 118140960795 + 80224 * 2 ^ 59
def prefixEnd_80224 : Nat := 4983230072969 + 3 ^ 40 * 80224 * 2
def baseEnd_80224 : Nat := 12205473193007216868463

theorem tailTrace_80224 : CollatzResearch.WordTrace tailWord_80224 prefixEnd_80224 12205473193007216868463 := by
  unfold tailWord_80224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463004830684812006751863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1950673107579749342335817 1463004830684812006751863)
  ·
    refine ⟨2194507246027218010127795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1463004830684812006751863 2194507246027218010127795)
    ·
      refine ⟨3291760869040827015191693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2194507246027218010127795 3291760869040827015191693)
      ·
        refine ⟨1234410325890310130696885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3291760869040827015191693 1234410325890310130696885)
        ·
          refine ⟨115725968052216574752833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1234410325890310130696885 115725968052216574752833)
          ·
            refine ⟨86794476039162431064625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115725968052216574752833 86794476039162431064625)
            ·
              refine ⟨65095857029371823298469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86794476039162431064625 65095857029371823298469)
              ·
                refine ⟨12205473193007216868463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65095857029371823298469 12205473193007216868463)
                ·
                  rfl

theorem cell20_80224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_80224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80224 prefixEnd_80224 := by exact prefixLift 80224
  have htrace : WordTrace (prefixWord ++ tailWord_80224) baseStart_80224 baseEnd_80224 := by
    simpa [prefixWord, tailWord_80224, baseEnd_80224] using wordTrace_append hprefix tailTrace_80224
  have hstable : (prefixWord ++ tailWord_80224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80224).length < 2 ^ (prefixWord ++ tailWord_80224).sum := by decide
  have hdescent : baseEnd_80224 < baseStart_80224 := by decide
  rcases family_descends (prefixWord ++ tailWord_80224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80228 : List Nat := [2, 3, 1, 1, 3, 1, 3, 6]
def baseStart_80228 : Nat := 118140960795 + 80228 * 2 ^ 59
def prefixEnd_80228 : Nat := 4983230072969 + 3 ^ 40 * 80228 * 2
def baseEnd_80228 : Nat := 12206081762671804824013

theorem tailTrace_80228 : CollatzResearch.WordTrace tailWord_80228 prefixEnd_80228 12206081762671804824013 := by
  unfold tailWord_80228
  simp only [CollatzResearch.WordTrace]
  refine ⟨1463077776677566348324669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1950770368903421797766225 1463077776677566348324669)
  ·
    refine ⟨548654166254087380621751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1463077776677566348324669 548654166254087380621751)
    ·
      refine ⟨822981249381131070932627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 548654166254087380621751 822981249381131070932627)
      ·
        refine ⟨1234471874071696606398941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 822981249381131070932627 1234471874071696606398941)
        ·
          refine ⟨462926952776886227399603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1234471874071696606398941 462926952776886227399603)
          ·
            refine ⟨694390429165329341099405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 462926952776886227399603 694390429165329341099405)
            ·
              refine ⟨260396410936998502912277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 694390429165329341099405 260396410936998502912277)
              ·
                refine ⟨12206081762671804824013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 260396410936998502912277 12206081762671804824013)
                ·
                  rfl

theorem cell20_80228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 3, 6].length) (baseStart_80228 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80228 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80228 prefixEnd_80228 := by exact prefixLift 80228
  have htrace : WordTrace (prefixWord ++ tailWord_80228) baseStart_80228 baseEnd_80228 := by
    simpa [prefixWord, tailWord_80228, baseEnd_80228] using wordTrace_append hprefix tailTrace_80228
  have hstable : (prefixWord ++ tailWord_80228).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80228).length < 2 ^ (prefixWord ++ tailWord_80228).sum := by decide
  have hdescent : baseEnd_80228 < baseStart_80228 := by decide
  rcases family_descends (prefixWord ++ tailWord_80228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80234 : List Nat := [3, 1, 3, 3, 1, 3, 1, 3, 2]
def baseStart_80234 : Nat := 118140960795 + 80234 * 2 ^ 59
def prefixEnd_80234 : Nat := 4983230072969 + 3 ^ 40 * 80234 * 2
def baseEnd_80234 : Nat := 36620983851506060272015

theorem tailTrace_80234 : CollatzResearch.WordTrace tailWord_80234 prefixEnd_80234 36620983851506060272015 := by
  unfold tailWord_80234
  simp only [CollatzResearch.WordTrace]
  refine ⟨731593597833348930341939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1950916260888930480911837 731593597833348930341939)
  ·
    refine ⟨1097390396750023395512909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 731593597833348930341939 1097390396750023395512909)
    ·
      refine ⟨411521398781258773317341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1097390396750023395512909 411521398781258773317341)
      ·
        refine ⟨154320524542972039994003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411521398781258773317341 154320524542972039994003)
        ·
          refine ⟨231480786814458059991005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154320524542972039994003 231480786814458059991005)
          ·
            refine ⟨86805295055421772496627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231480786814458059991005 86805295055421772496627)
            ·
              refine ⟨130207942583132658744941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86805295055421772496627 130207942583132658744941)
              ·
                refine ⟨48827978468674747029353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130207942583132658744941 48827978468674747029353)
                ·
                  refine ⟨36620983851506060272015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48827978468674747029353 36620983851506060272015)
                  ·
                    rfl

theorem cell20_80234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 3, 1, 3, 2].length) (baseStart_80234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80234 prefixEnd_80234 := by exact prefixLift 80234
  have htrace : WordTrace (prefixWord ++ tailWord_80234) baseStart_80234 baseEnd_80234 := by
    simpa [prefixWord, tailWord_80234, baseEnd_80234] using wordTrace_append hprefix tailTrace_80234
  have hstable : (prefixWord ++ tailWord_80234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80234).length < 2 ^ (prefixWord ++ tailWord_80234).sum := by decide
  have hdescent : baseEnd_80234 < baseStart_80234 := by decide
  rcases family_descends (prefixWord ++ tailWord_80234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80245 : List Nat := [1, 3, 4, 1, 2, 3, 6]
def baseStart_80245 : Nat := 118140960795 + 80245 * 2 ^ 59
def prefixEnd_80245 : Nat := 4983230072969 + 3 ^ 40 * 80245 * 2
def baseEnd_80245 : Nat := 4069556061248767878367

theorem tailTrace_80245 : CollatzResearch.WordTrace tailWord_80245 prefixEnd_80245 4069556061248767878367 := by
  unfold tailWord_80245
  simp only [CollatzResearch.WordTrace]
  refine ⟨2926775594293544600018189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1951183729529029733345459 2926775594293544600018189)
  ·
    refine ⟨1097540847860079225006821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2926775594293544600018189 1097540847860079225006821)
    ·
      refine ⟨205788908973764854688779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1097540847860079225006821 205788908973764854688779)
      ·
        refine ⟨308683363460647282033169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205788908973764854688779 308683363460647282033169)
        ·
          refine ⟨231512522595485461524877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308683363460647282033169 231512522595485461524877)
          ·
            refine ⟨86817195973307048071829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231512522595485461524877 86817195973307048071829)
            ·
              refine ⟨4069556061248767878367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 86817195973307048071829 4069556061248767878367)
              ·
                rfl

theorem cell20_80245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_80245 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80245 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80245 prefixEnd_80245 := by exact prefixLift 80245
  have htrace : WordTrace (prefixWord ++ tailWord_80245) baseStart_80245 baseEnd_80245 := by
    simpa [prefixWord, tailWord_80245, baseEnd_80245] using wordTrace_append hprefix tailTrace_80245
  have hstable : (prefixWord ++ tailWord_80245).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80245).length < 2 ^ (prefixWord ++ tailWord_80245).sum := by decide
  have hdescent : baseEnd_80245 < baseStart_80245 := by decide
  rcases family_descends (prefixWord ++ tailWord_80245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80328 : List Nat := [2, 1, 3, 1, 3, 2, 2, 3, 3]
def baseStart_80328 : Nat := 118140960795 + 80328 * 2 ^ 59
def prefixEnd_80328 : Nat := 4983230072969 + 3 ^ 40 * 80328 * 2
def baseEnd_80328 : Nat := 36663888012859511138297

theorem tailTrace_80328 : CollatzResearch.WordTrace tailWord_80328 prefixEnd_80328 36663888012859511138297 := by
  unfold tailWord_80328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1464901426496424887644819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1953201901995233183526425 1464901426496424887644819)
  ·
    refine ⟨2197352139744637331467229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1464901426496424887644819 2197352139744637331467229)
    ·
      refine ⟨824007052404238999300211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2197352139744637331467229 824007052404238999300211)
      ·
        refine ⟨1236010578606358498950317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 824007052404238999300211 1236010578606358498950317)
        ·
          refine ⟨463503966977384437106369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1236010578606358498950317 463503966977384437106369)
          ·
            refine ⟨347627975233038327829777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463503966977384437106369 347627975233038327829777)
            ·
              refine ⟨260720981424778745872333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347627975233038327829777 260720981424778745872333)
              ·
                refine ⟨97770368034292029702125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260720981424778745872333 97770368034292029702125)
                ·
                  refine ⟨36663888012859511138297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97770368034292029702125 36663888012859511138297)
                  ·
                    rfl

theorem cell20_80328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 3, 3].length) (baseStart_80328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80328 prefixEnd_80328 := by exact prefixLift 80328
  have htrace : WordTrace (prefixWord ++ tailWord_80328) baseStart_80328 baseEnd_80328 := by
    simpa [prefixWord, tailWord_80328, baseEnd_80328] using wordTrace_append hprefix tailTrace_80328
  have hstable : (prefixWord ++ tailWord_80328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80328).length < 2 ^ (prefixWord ++ tailWord_80328).sum := by decide
  have hdescent : baseEnd_80328 < baseStart_80328 := by decide
  rcases family_descends (prefixWord ++ tailWord_80328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80352 : List Nat := [2, 1, 1, 3, 1, 1, 6, 3, 2]
def baseStart_80352 : Nat := 118140960795 + 80352 * 2 ^ 59
def prefixEnd_80352 : Nat := 4983230072969 + 3 ^ 40 * 80352 * 2
def baseEnd_80352 : Nat := 36674842266822094338199

theorem tailTrace_80352 : CollatzResearch.WordTrace tailWord_80352 prefixEnd_80352 36674842266822094338199 := by
  unfold tailWord_80352
  simp only [CollatzResearch.WordTrace]
  refine ⟨1465339102452950937081655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1953785469937267916108873 1465339102452950937081655)
  ·
    refine ⟨2198008653679426405622483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1465339102452950937081655 2198008653679426405622483)
    ·
      refine ⟨3297012980519139608433725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2198008653679426405622483 3297012980519139608433725)
      ·
        refine ⟨1236379867694677353162647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3297012980519139608433725 1236379867694677353162647)
        ·
          refine ⟨1854569801542016029743971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1236379867694677353162647 1854569801542016029743971)
          ·
            refine ⟨2781854702313024044615957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1854569801542016029743971 2781854702313024044615957)
            ·
              refine ⟨130399439170923002091373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2781854702313024044615957 130399439170923002091373)
              ·
                refine ⟨48899789689096125784265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130399439170923002091373 48899789689096125784265)
                ·
                  refine ⟨36674842266822094338199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48899789689096125784265 36674842266822094338199)
                  ·
                    rfl

theorem cell20_80352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 6, 3, 2].length) (baseStart_80352 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80352 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80352 prefixEnd_80352 := by exact prefixLift 80352
  have htrace : WordTrace (prefixWord ++ tailWord_80352) baseStart_80352 baseEnd_80352 := by
    simpa [prefixWord, tailWord_80352, baseEnd_80352] using wordTrace_append hprefix tailTrace_80352
  have hstable : (prefixWord ++ tailWord_80352).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80352).length < 2 ^ (prefixWord ++ tailWord_80352).sum := by decide
  have hdescent : baseEnd_80352 < baseStart_80352 := by decide
  rcases family_descends (prefixWord ++ tailWord_80352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80363 : List Nat := [1, 1, 1, 1, 2, 3, 11]
def baseStart_80363 : Nat := 118140960795 + 80363 * 2 ^ 59
def prefixEnd_80363 : Nat := 4983230072969 + 3 ^ 40 * 80363 * 2
def baseEnd_80363 : Nat := 4075540329617216107943

theorem tailTrace_80363 : CollatzResearch.WordTrace tailWord_80363 prefixEnd_80363 4075540329617216107943 := by
  unfold tailWord_80363
  simp only [CollatzResearch.WordTrace]
  refine ⟨2931079407866050752813743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1954052938577367168542495 2931079407866050752813743)
  ·
    refine ⟨4396619111799076129220615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2931079407866050752813743 4396619111799076129220615)
    ·
      refine ⟨6594928667698614193830923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4396619111799076129220615 6594928667698614193830923)
      ·
        refine ⟨9892393001547921290746385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6594928667698614193830923 9892393001547921290746385)
        ·
          refine ⟨7419294751160940968059789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9892393001547921290746385 7419294751160940968059789)
          ·
            refine ⟨2782235531685352863022421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7419294751160940968059789 2782235531685352863022421)
            ·
              refine ⟨4075540329617216107943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2782235531685352863022421 4075540329617216107943)
              ·
                rfl

theorem cell20_80363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 11].length) (baseStart_80363 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80363 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80363 prefixEnd_80363 := by exact prefixLift 80363
  have htrace : WordTrace (prefixWord ++ tailWord_80363) baseStart_80363 baseEnd_80363 := by
    simpa [prefixWord, tailWord_80363, baseEnd_80363] using wordTrace_append hprefix tailTrace_80363
  have hstable : (prefixWord ++ tailWord_80363).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80363).length < 2 ^ (prefixWord ++ tailWord_80363).sum := by decide
  have hdescent : baseEnd_80363 < baseStart_80363 := by decide
  rcases family_descends (prefixWord ++ tailWord_80363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80366 : List Nat := [4, 1, 2, 1, 2, 3, 1, 1, 5]
def baseStart_80366 : Nat := 118140960795 + 80366 * 2 ^ 59
def prefixEnd_80366 : Nat := 4983230072969 + 3 ^ 40 * 80366 * 2
def baseEnd_80366 : Nat := 36681232248300267871475

theorem tailTrace_80366 : CollatzResearch.WordTrace tailWord_80366 prefixEnd_80366 36681232248300267871475 := by
  unfold tailWord_80366
  simp only [CollatzResearch.WordTrace]
  refine ⟨366398603356897783146619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1954125884570121510115301 366398603356897783146619)
  ·
    refine ⟨549597905035346674719929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 366398603356897783146619 549597905035346674719929)
    ·
      refine ⟨412198428776510006039947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 549597905035346674719929 412198428776510006039947)
      ·
        refine ⟨618297643164765009059921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412198428776510006039947 618297643164765009059921)
        ·
          refine ⟨463723232373573756794941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 618297643164765009059921 463723232373573756794941)
          ·
            refine ⟨173896212140090158798103, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463723232373573756794941 173896212140090158798103)
            ·
              refine ⟨260844318210135238197155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173896212140090158798103 260844318210135238197155)
              ·
                refine ⟨391266477315202857295733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260844318210135238197155 391266477315202857295733)
                ·
                  refine ⟨36681232248300267871475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 391266477315202857295733 36681232248300267871475)
                  ·
                    rfl

theorem cell20_80366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 1, 5].length) (baseStart_80366 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80366 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80366 prefixEnd_80366 := by exact prefixLift 80366
  have htrace : WordTrace (prefixWord ++ tailWord_80366) baseStart_80366 baseEnd_80366 := by
    simpa [prefixWord, tailWord_80366, baseEnd_80366] using wordTrace_append hprefix tailTrace_80366
  have hstable : (prefixWord ++ tailWord_80366).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80366).length < 2 ^ (prefixWord ++ tailWord_80366).sum := by decide
  have hdescent : baseEnd_80366 < baseStart_80366 := by decide
  rcases family_descends (prefixWord ++ tailWord_80366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80424 : List Nat := [2, 1, 5, 2, 1, 2, 3, 2, 2]
def baseStart_80424 : Nat := 118140960795 + 80424 * 2 ^ 59
def prefixEnd_80424 : Nat := 4983230072969 + 3 ^ 40 * 80424 * 2
def baseEnd_80424 : Nat := 36707705028709843937905

theorem tailTrace_80424 : CollatzResearch.WordTrace tailWord_80424 prefixEnd_80424 36707705028709843937905 := by
  unfold tailWord_80424
  simp only [CollatzResearch.WordTrace]
  refine ⟨1466652130322529085392163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1955536173763372113856217 1466652130322529085392163)
  ·
    refine ⟨2199978195483793628088245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1466652130322529085392163 2199978195483793628088245)
    ·
      refine ⟨206247955826605652633273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2199978195483793628088245 206247955826605652633273)
      ·
        refine ⟨154685966869954239474955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206247955826605652633273 154685966869954239474955)
        ·
          refine ⟨232028950304931359212433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154685966869954239474955 232028950304931359212433)
          ·
            refine ⟨174021712728698519409325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 232028950304931359212433 174021712728698519409325)
            ·
              refine ⟨65258142273261944778497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174021712728698519409325 65258142273261944778497)
              ·
                refine ⟨48943606704946458583873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65258142273261944778497 48943606704946458583873)
                ·
                  refine ⟨36707705028709843937905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48943606704946458583873 36707705028709843937905)
                  ·
                    rfl

theorem cell20_80424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 2, 2].length) (baseStart_80424 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80424 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80424 prefixEnd_80424 := by exact prefixLift 80424
  have htrace : WordTrace (prefixWord ++ tailWord_80424) baseStart_80424 baseEnd_80424 := by
    simpa [prefixWord, tailWord_80424, baseEnd_80424] using wordTrace_append hprefix tailTrace_80424
  have hstable : (prefixWord ++ tailWord_80424).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80424).length < 2 ^ (prefixWord ++ tailWord_80424).sum := by decide
  have hdescent : baseEnd_80424 < baseStart_80424 := by decide
  rcases family_descends (prefixWord ++ tailWord_80424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80438 : List Nat := [5, 1, 2, 1, 2, 1, 4, 1, 3]
def baseStart_80438 : Nat := 118140960795 + 80438 * 2 ^ 59
def prefixEnd_80438 : Nat := 4983230072969 + 3 ^ 40 * 80438 * 2
def baseEnd_80438 : Nat := 36714095010188017471181

theorem tailTrace_80438 : CollatzResearch.WordTrace tailWord_80438 prefixEnd_80438 36714095010188017471181 := by
  unfold tailWord_80438
  simp only [CollatzResearch.WordTrace]
  refine ⟨183363430162146160112123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1955876588396225707862645 183363430162146160112123)
  ·
    refine ⟨275045145243219240168185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183363430162146160112123 275045145243219240168185)
    ·
      refine ⟨206283858932414430126139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 275045145243219240168185 206283858932414430126139)
      ·
        refine ⟨309425788398621645189209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206283858932414430126139 309425788398621645189209)
        ·
          refine ⟨232069341298966233891907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309425788398621645189209 232069341298966233891907)
          ·
            refine ⟨348104011948449350837861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232069341298966233891907 348104011948449350837861)
            ·
              refine ⟨65269502240334253282099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348104011948449350837861 65269502240334253282099)
              ·
                refine ⟨97904253360501379923149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65269502240334253282099 97904253360501379923149)
                ·
                  refine ⟨36714095010188017471181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97904253360501379923149 36714095010188017471181)
                  ·
                    rfl

theorem cell20_80438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 4, 1, 3].length) (baseStart_80438 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80438 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80438 prefixEnd_80438 := by exact prefixLift 80438
  have htrace : WordTrace (prefixWord ++ tailWord_80438) baseStart_80438 baseEnd_80438 := by
    simpa [prefixWord, tailWord_80438, baseEnd_80438] using wordTrace_append hprefix tailTrace_80438
  have hstable : (prefixWord ++ tailWord_80438).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80438).length < 2 ^ (prefixWord ++ tailWord_80438).sum := by decide
  have hdescent : baseEnd_80438 < baseStart_80438 := by decide
  rcases family_descends (prefixWord ++ tailWord_80438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80442 : List Nat := [3, 1, 1, 1, 3, 4, 1, 3, 3]
def baseStart_80442 : Nat := 118140960795 + 80442 * 2 ^ 59
def prefixEnd_80442 : Nat := 4983230072969 + 3 ^ 40 * 80442 * 2
def baseEnd_80442 : Nat := 36715920719181781337831

theorem tailTrace_80442 : CollatzResearch.WordTrace tailWord_80442 prefixEnd_80442 36715920719181781337831 := by
  unfold tailWord_80442
  simp only [CollatzResearch.WordTrace]
  refine ⟨733490193644961811234895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1955973849719898163293053 733490193644961811234895)
  ·
    refine ⟨1100235290467442716852343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 733490193644961811234895 1100235290467442716852343)
    ·
      refine ⟨1650352935701164075278515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1100235290467442716852343 1650352935701164075278515)
      ·
        refine ⟨2475529403551746112917773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1650352935701164075278515 2475529403551746112917773)
        ·
          refine ⟨928323526331904792344165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2475529403551746112917773 928323526331904792344165)
          ·
            refine ⟨174060661187232148564531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 928323526331904792344165 174060661187232148564531)
            ·
              refine ⟨261090991780848222846797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174060661187232148564531 261090991780848222846797)
              ·
                refine ⟨97909121917818083567549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 261090991780848222846797 97909121917818083567549)
                ·
                  refine ⟨36715920719181781337831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97909121917818083567549 36715920719181781337831)
                  ·
                    rfl

theorem cell20_80442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 4, 1, 3, 3].length) (baseStart_80442 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80442 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80442 prefixEnd_80442 := by exact prefixLift 80442
  have htrace : WordTrace (prefixWord ++ tailWord_80442) baseStart_80442 baseEnd_80442 := by
    simpa [prefixWord, tailWord_80442, baseEnd_80442] using wordTrace_append hprefix tailTrace_80442
  have hstable : (prefixWord ++ tailWord_80442).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80442).length < 2 ^ (prefixWord ++ tailWord_80442).sum := by decide
  have hdescent : baseEnd_80442 < baseStart_80442 := by decide
  rcases family_descends (prefixWord ++ tailWord_80442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80466 : List Nat := [3, 2, 2, 1, 2, 1, 2, 5, 2]
def baseStart_80466 : Nat := 118140960795 + 80466 * 2 ^ 59
def prefixEnd_80466 : Nat := 4983230072969 + 3 ^ 40 * 80466 * 2
def baseEnd_80466 : Nat := 36726874973144364537733

theorem tailTrace_80466 : CollatzResearch.WordTrace tailWord_80466 prefixEnd_80466 36726874973144364537733 := by
  unfold tailWord_80466
  simp only [CollatzResearch.WordTrace]
  refine ⟨733709031623224835953313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1956557417661932895875501 733709031623224835953313)
  ·
    refine ⟨550281773717418626964985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 733709031623224835953313 550281773717418626964985)
    ·
      refine ⟨412711330288063970223739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 550281773717418626964985 412711330288063970223739)
      ·
        refine ⟨619066995432095955335609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412711330288063970223739 619066995432095955335609)
        ·
          refine ⟨464300246574071966501707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 619066995432095955335609 464300246574071966501707)
          ·
            refine ⟨696450369861107949752561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464300246574071966501707 696450369861107949752561)
            ·
              refine ⟨522337777395830962314421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 696450369861107949752561 522337777395830962314421)
              ·
                refine ⟨48969166630859152716977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 522337777395830962314421 48969166630859152716977)
                ·
                  refine ⟨36726874973144364537733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48969166630859152716977 36726874973144364537733)
                  ·
                    rfl

theorem cell20_80466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 2, 5, 2].length) (baseStart_80466 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80466 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80466 prefixEnd_80466 := by exact prefixLift 80466
  have htrace : WordTrace (prefixWord ++ tailWord_80466) baseStart_80466 baseEnd_80466 := by
    simpa [prefixWord, tailWord_80466, baseEnd_80466] using wordTrace_append hprefix tailTrace_80466
  have hstable : (prefixWord ++ tailWord_80466).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80466).length < 2 ^ (prefixWord ++ tailWord_80466).sum := by decide
  have hdescent : baseEnd_80466 < baseStart_80466 := by decide
  rcases family_descends (prefixWord ++ tailWord_80466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80508 : List Nat := [2, 2, 2, 1, 1, 2, 3, 1, 6]
def baseStart_80508 : Nat := 118140960795 + 80508 * 2 ^ 59
def prefixEnd_80508 : Nat := 4983230072969 + 3 ^ 40 * 80508 * 2
def baseEnd_80508 : Nat := 36746044917578885137561

theorem tailTrace_80508 : CollatzResearch.WordTrace tailWord_80508 prefixEnd_80508 36746044917578885137561 := by
  unfold tailWord_80508
  simp only [CollatzResearch.WordTrace]
  refine ⟨1468183996170370258421089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1957578661560493677894785 1468183996170370258421089)
  ·
    refine ⟨1101137997127777693815817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1468183996170370258421089 1101137997127777693815817)
    ·
      refine ⟨825853497845833270361863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1101137997127777693815817 825853497845833270361863)
      ·
        refine ⟨1238780246768749905542795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 825853497845833270361863 1238780246768749905542795)
        ·
          refine ⟨1858170370153124858314193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1238780246768749905542795 1858170370153124858314193)
          ·
            refine ⟨1393627777614843643735645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1858170370153124858314193 1393627777614843643735645)
            ·
              refine ⟨522610416605566366400867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1393627777614843643735645 522610416605566366400867)
              ·
                refine ⟨783915624908349549601301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 522610416605566366400867 783915624908349549601301)
                ·
                  refine ⟨36746044917578885137561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 783915624908349549601301 36746044917578885137561)
                  ·
                    rfl

theorem cell20_80508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 1, 6].length) (baseStart_80508 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80508 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80508 prefixEnd_80508 := by exact prefixLift 80508
  have htrace : WordTrace (prefixWord ++ tailWord_80508) baseStart_80508 baseEnd_80508 := by
    simpa [prefixWord, tailWord_80508, baseEnd_80508] using wordTrace_append hprefix tailTrace_80508
  have hstable : (prefixWord ++ tailWord_80508).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80508).length < 2 ^ (prefixWord ++ tailWord_80508).sum := by decide
  have hdescent : baseEnd_80508 < baseStart_80508 := by decide
  rcases family_descends (prefixWord ++ tailWord_80508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80515 : List Nat := [1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_80515 : Nat := 118140960795 + 80515 * 2 ^ 59
def prefixEnd_80515 : Nat := 4983230072969 + 3 ^ 40 * 80515 * 2
def baseEnd_80515 : Nat := 12249746636105990634733

theorem tailTrace_80515 : CollatzResearch.WordTrace tailWord_80515 prefixEnd_80515 12249746636105990634733 := by
  unfold tailWord_80515
  simp only [CollatzResearch.WordTrace]
  refine ⟨2936623303315380712346999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1957748868876920474897999 2936623303315380712346999)
  ·
    refine ⟨4404934954973071068520499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2936623303315380712346999 4404934954973071068520499)
    ·
      refine ⟨6607402432459606602780749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4404934954973071068520499 6607402432459606602780749)
      ·
        refine ⟨2477775912172352476042781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6607402432459606602780749 2477775912172352476042781)
        ·
          refine ⟨929165967064632178516043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2477775912172352476042781 929165967064632178516043)
          ·
            refine ⟨1393748950596948267774065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 929165967064632178516043 1393748950596948267774065)
            ·
              refine ⟨1045311712947711200830549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1393748950596948267774065 1045311712947711200830549)
              ·
                refine ⟨12249746636105990634733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1045311712947711200830549 12249746636105990634733)
                ·
                  rfl

theorem cell20_80515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_80515 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80515 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80515 prefixEnd_80515 := by exact prefixLift 80515
  have htrace : WordTrace (prefixWord ++ tailWord_80515) baseStart_80515 baseEnd_80515 := by
    simpa [prefixWord, tailWord_80515, baseEnd_80515] using wordTrace_append hprefix tailTrace_80515
  have hstable : (prefixWord ++ tailWord_80515).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80515).length < 2 ^ (prefixWord ++ tailWord_80515).sum := by decide
  have hdescent : baseEnd_80515 < baseStart_80515 := by decide
  rcases family_descends (prefixWord ++ tailWord_80515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80542 : List Nat := [4, 3, 1, 1, 1, 1, 4, 1, 4]
def baseStart_80542 : Nat := 118140960795 + 80542 * 2 ^ 59
def prefixEnd_80542 : Nat := 4983230072969 + 3 ^ 40 * 80542 * 2
def baseEnd_80542 : Nat := 36761563444025878004089

theorem tailTrace_80542 : CollatzResearch.WordTrace tailWord_80542 prefixEnd_80542 36761563444025878004089 := by
  unfold tailWord_80542
  simp only [CollatzResearch.WordTrace]
  refine ⟨367201009277195540447485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1958405382811709549053253 367201009277195540447485)
  ·
    refine ⟨137700378478948327667807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 367201009277195540447485 137700378478948327667807)
    ·
      refine ⟨206550567718422491501711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137700378478948327667807 206550567718422491501711)
      ·
        refine ⟨309825851577633737252567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206550567718422491501711 309825851577633737252567)
        ·
          refine ⟨464738777366450605878851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309825851577633737252567 464738777366450605878851)
          ·
            refine ⟨697108166049675908818277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 464738777366450605878851 697108166049675908818277)
            ·
              refine ⟨130707781134314232903427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 697108166049675908818277 130707781134314232903427)
              ·
                refine ⟨196061671701471349355141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130707781134314232903427 196061671701471349355141)
                ·
                  refine ⟨36761563444025878004089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196061671701471349355141 36761563444025878004089)
                  ·
                    rfl

theorem cell20_80542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_80542 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80542 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80542 prefixEnd_80542 := by exact prefixLift 80542
  have htrace : WordTrace (prefixWord ++ tailWord_80542) baseStart_80542 baseEnd_80542 := by
    simpa [prefixWord, tailWord_80542, baseEnd_80542] using wordTrace_append hprefix tailTrace_80542
  have hstable : (prefixWord ++ tailWord_80542).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80542).length < 2 ^ (prefixWord ++ tailWord_80542).sum := by decide
  have hdescent : baseEnd_80542 < baseStart_80542 := by decide
  rcases family_descends (prefixWord ++ tailWord_80542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80566 : List Nat := [5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_80566 : Nat := 118140960795 + 80566 * 2 ^ 59
def prefixEnd_80566 : Nat := 4983230072969 + 3 ^ 40 * 80566 * 2
def baseEnd_80566 : Nat := 12257505899329487067997

theorem tailTrace_80566 : CollatzResearch.WordTrace tailWord_80566 prefixEnd_80566 12257505899329487067997 := by
  unfold tailWord_80566
  simp only [CollatzResearch.WordTrace]
  refine ⟨183655214133163526403347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1958988950753744281635701 183655214133163526403347)
  ·
    refine ⟨275482821199745289605021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183655214133163526403347 275482821199745289605021)
    ·
      refine ⟨103306057949904483601883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 275482821199745289605021 103306057949904483601883)
      ·
        refine ⟨154959086924856725402825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103306057949904483601883 154959086924856725402825)
        ·
          refine ⟨116219315193642544052119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154959086924856725402825 116219315193642544052119)
          ·
            refine ⟨174328972790463816078179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116219315193642544052119 174328972790463816078179)
            ·
              refine ⟨261493459185695724117269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 174328972790463816078179 261493459185695724117269)
              ·
                refine ⟨12257505899329487067997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 261493459185695724117269 12257505899329487067997)
                ·
                  rfl

theorem cell20_80566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_80566 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80566 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80566 prefixEnd_80566 := by exact prefixLift 80566
  have htrace : WordTrace (prefixWord ++ tailWord_80566) baseStart_80566 baseEnd_80566 := by
    simpa [prefixWord, tailWord_80566, baseEnd_80566] using wordTrace_append hprefix tailTrace_80566
  have hstable : (prefixWord ++ tailWord_80566).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80566).length < 2 ^ (prefixWord ++ tailWord_80566).sum := by decide
  have hdescent : baseEnd_80566 < baseStart_80566 := by decide
  rcases family_descends (prefixWord ++ tailWord_80566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80597 : List Nat := [1, 3, 2, 5, 1, 2, 1, 1, 4]
def baseStart_80597 : Nat := 118140960795 + 80597 * 2 ^ 59
def prefixEnd_80597 : Nat := 4983230072969 + 3 ^ 40 * 80597 * 2
def baseEnd_80597 : Nat := 36786666942690131170531

theorem tailTrace_80597 : CollatzResearch.WordTrace tailWord_80597 prefixEnd_80597 36786666942690131170531 := by
  unfold tailWord_80597
  simp only [CollatzResearch.WordTrace]
  refine ⟨2939614089018308716832045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1959742726012205811221363 2939614089018308716832045)
  ·
    refine ⟨1102355283381865768812017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2939614089018308716832045 1102355283381865768812017)
    ·
      refine ⟨826766462536399326609013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1102355283381865768812017 826766462536399326609013)
      ·
        refine ⟨77509355862787436869595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 826766462536399326609013 77509355862787436869595)
        ·
          refine ⟨116264033794181155304393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77509355862787436869595 116264033794181155304393)
          ·
            refine ⟨87198025345635866478295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116264033794181155304393 87198025345635866478295)
            ·
              refine ⟨130797038018453799717443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87198025345635866478295 130797038018453799717443)
              ·
                refine ⟨196195557027680699576165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130797038018453799717443 196195557027680699576165)
                ·
                  refine ⟨36786666942690131170531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196195557027680699576165 36786666942690131170531)
                  ·
                    rfl

theorem cell20_80597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 5, 1, 2, 1, 1, 4].length) (baseStart_80597 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80597 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80597 prefixEnd_80597 := by exact prefixLift 80597
  have htrace : WordTrace (prefixWord ++ tailWord_80597) baseStart_80597 baseEnd_80597 := by
    simpa [prefixWord, tailWord_80597, baseEnd_80597] using wordTrace_append hprefix tailTrace_80597
  have hstable : (prefixWord ++ tailWord_80597).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80597).length < 2 ^ (prefixWord ++ tailWord_80597).sum := by decide
  have hdescent : baseEnd_80597 < baseStart_80597 := by decide
  rcases family_descends (prefixWord ++ tailWord_80597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80611 : List Nat := [1, 1, 1, 7, 1, 1, 4, 1, 3]
def baseStart_80611 : Nat := 118140960795 + 80611 * 2 ^ 59
def prefixEnd_80611 : Nat := 4983230072969 + 3 ^ 40 * 80611 * 2
def baseEnd_80611 : Nat := 36793056924168304703807

theorem tailTrace_80611 : CollatzResearch.WordTrace tailWord_80611 prefixEnd_80611 36793056924168304703807 := by
  unfold tailWord_80611
  simp only [CollatzResearch.WordTrace]
  refine ⟨2940124710967589107841687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1960083140645059405227791 2940124710967589107841687)
  ·
    refine ⟨4410187066451383661762531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2940124710967589107841687 4410187066451383661762531)
    ·
      refine ⟨6615280599677075492643797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4410187066451383661762531 6615280599677075492643797)
      ·
        refine ⟨155045639054931456858839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6615280599677075492643797 155045639054931456858839)
        ·
          refine ⟨232568458582397185288259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155045639054931456858839 232568458582397185288259)
          ·
            refine ⟨348852687873595777932389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 232568458582397185288259 348852687873595777932389)
            ·
              refine ⟨65409878976299208362323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 348852687873595777932389 65409878976299208362323)
              ·
                refine ⟨98114818464448812543485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65409878976299208362323 98114818464448812543485)
                ·
                  refine ⟨36793056924168304703807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98114818464448812543485 36793056924168304703807)
                  ·
                    rfl

theorem cell20_80611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 4, 1, 3].length) (baseStart_80611 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80611 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80611 prefixEnd_80611 := by exact prefixLift 80611
  have htrace : WordTrace (prefixWord ++ tailWord_80611) baseStart_80611 baseEnd_80611 := by
    simpa [prefixWord, tailWord_80611, baseEnd_80611] using wordTrace_append hprefix tailTrace_80611
  have hstable : (prefixWord ++ tailWord_80611).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80611).length < 2 ^ (prefixWord ++ tailWord_80611).sum := by decide
  have hdescent : baseEnd_80611 < baseStart_80611 := by decide
  rcases family_descends (prefixWord ++ tailWord_80611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80639 : List Nat := [1, 1, 2, 2, 1, 3, 1, 7, 2]
def baseStart_80639 : Nat := 118140960795 + 80639 * 2 ^ 59
def prefixEnd_80639 : Nat := 4983230072969 + 3 ^ 40 * 80639 * 2
def baseEnd_80639 : Nat := 36805836887124651770359

theorem tailTrace_80639 : CollatzResearch.WordTrace tailWord_80639 prefixEnd_80639 36805836887124651770359 := by
  unfold tailWord_80639
  simp only [CollatzResearch.WordTrace]
  refine ⟨2941145954866149889860971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1960763969910766593240647 2941145954866149889860971)
  ·
    refine ⟨4411718932299224834791457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2941145954866149889860971 4411718932299224834791457)
    ·
      refine ⟨3308789199224418626093593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4411718932299224834791457 3308789199224418626093593)
      ·
        refine ⟨2481591899418313969570195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3308789199224418626093593 2481591899418313969570195)
        ·
          refine ⟨3722387849127470954355293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2481591899418313969570195 3722387849127470954355293)
          ·
            refine ⟨1395895443422801607883235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3722387849127470954355293 1395895443422801607883235)
            ·
              refine ⟨2093843165134202411824853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1395895443422801607883235 2093843165134202411824853)
              ·
                refine ⟨49074449182832869027145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2093843165134202411824853 49074449182832869027145)
                ·
                  refine ⟨36805836887124651770359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49074449182832869027145 36805836887124651770359)
                  ·
                    rfl

theorem cell20_80639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 7, 2].length) (baseStart_80639 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80639 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80639 prefixEnd_80639 := by exact prefixLift 80639
  have htrace : WordTrace (prefixWord ++ tailWord_80639) baseStart_80639 baseEnd_80639 := by
    simpa [prefixWord, tailWord_80639, baseEnd_80639] using wordTrace_append hprefix tailTrace_80639
  have hstable : (prefixWord ++ tailWord_80639).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80639).length < 2 ^ (prefixWord ++ tailWord_80639).sum := by decide
  have hdescent : baseEnd_80639 < baseStart_80639 := by decide
  rcases family_descends (prefixWord ++ tailWord_80639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80663 : List Nat := [1, 1, 3, 4, 3, 2, 1, 5]
def baseStart_80663 : Nat := 118140960795 + 80663 * 2 ^ 59
def prefixEnd_80663 : Nat := 4983230072969 + 3 ^ 40 * 80663 * 2
def baseEnd_80663 : Nat := 12272263713695744990087

theorem tailTrace_80663 : CollatzResearch.WordTrace tailWord_80663 prefixEnd_80663 12272263713695744990087 := by
  unfold tailWord_80663
  simp only [CollatzResearch.WordTrace]
  refine ⟨2942021306779201988734643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1961347537852801325823095 2942021306779201988734643)
  ·
    refine ⟨4413031960168802983101965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2942021306779201988734643 4413031960168802983101965)
    ·
      refine ⟨1654886985063301118663237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4413031960168802983101965 1654886985063301118663237)
      ·
        refine ⟨310291309699368959749357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1654886985063301118663237 310291309699368959749357)
        ·
          refine ⟨116359241137263359906009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 310291309699368959749357 116359241137263359906009)
          ·
            refine ⟨87269430852947519929507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116359241137263359906009 87269430852947519929507)
            ·
              refine ⟨130904146279421279894261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87269430852947519929507 130904146279421279894261)
              ·
                refine ⟨12272263713695744990087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130904146279421279894261 12272263713695744990087)
                ·
                  rfl

theorem cell20_80663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 2, 1, 5].length) (baseStart_80663 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80663 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80663 prefixEnd_80663 := by exact prefixLift 80663
  have htrace : WordTrace (prefixWord ++ tailWord_80663) baseStart_80663 baseEnd_80663 := by
    simpa [prefixWord, tailWord_80663, baseEnd_80663] using wordTrace_append hprefix tailTrace_80663
  have hstable : (prefixWord ++ tailWord_80663).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80663).length < 2 ^ (prefixWord ++ tailWord_80663).sum := by decide
  have hdescent : baseEnd_80663 < baseStart_80663 := by decide
  rcases family_descends (prefixWord ++ tailWord_80663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80684 : List Nat := [2, 2, 1, 1, 1, 4, 5, 4]
def baseStart_80684 : Nat := 118140960795 + 80684 * 2 ^ 59
def prefixEnd_80684 : Nat := 4983230072969 + 3 ^ 40 * 80684 * 2
def baseEnd_80684 : Nat := 12275458704434831756725

theorem tailTrace_80684 : CollatzResearch.WordTrace tailWord_80684 prefixEnd_80684 12275458704434831756725 := by
  unfold tailWord_80684
  simp only [CollatzResearch.WordTrace]
  refine ⟨1471393619851561287624553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1961858159802081716832737 1471393619851561287624553)
  ·
    refine ⟨1103545214888670965718415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1471393619851561287624553 1103545214888670965718415)
    ·
      refine ⟨1655317822333006448577623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1103545214888670965718415 1655317822333006448577623)
      ·
        refine ⟨2482976733499509672866435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1655317822333006448577623 2482976733499509672866435)
        ·
          refine ⟨3724465100249264509299653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2482976733499509672866435 3724465100249264509299653)
          ·
            refine ⟨698337206296737095493685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3724465100249264509299653 698337206296737095493685)
            ·
              refine ⟨65469113090319102702533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 698337206296737095493685 65469113090319102702533)
              ·
                refine ⟨12275458704434831756725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65469113090319102702533 12275458704434831756725)
                ·
                  rfl

theorem cell20_80684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_80684 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80684 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80684 prefixEnd_80684 := by exact prefixLift 80684
  have htrace : WordTrace (prefixWord ++ tailWord_80684) baseStart_80684 baseEnd_80684 := by
    simpa [prefixWord, tailWord_80684, baseEnd_80684] using wordTrace_append hprefix tailTrace_80684
  have hstable : (prefixWord ++ tailWord_80684).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80684).length < 2 ^ (prefixWord ++ tailWord_80684).sum := by decide
  have hdescent : baseEnd_80684 < baseStart_80684 := by decide
  rcases family_descends (prefixWord ++ tailWord_80684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80736 : List Nat := [2, 1, 1, 3, 3, 1, 1, 4, 4]
def baseStart_80736 : Nat := 118140960795 + 80736 * 2 ^ 59
def prefixEnd_80736 : Nat := 4983230072969 + 3 ^ 40 * 80736 * 2
def baseEnd_80736 : Nat := 36850110330223425536629

theorem tailTrace_80736 : CollatzResearch.WordTrace tailWord_80736 prefixEnd_80736 36850110330223425536629 := by
  unfold tailWord_80736
  simp only [CollatzResearch.WordTrace]
  refine ⟨1472341917757367728071031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1963122557009823637428041 1472341917757367728071031)
  ·
    refine ⟨2208512876636051592106547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1472341917757367728071031 2208512876636051592106547)
    ·
      refine ⟨3312769314954077388159821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2208512876636051592106547 3312769314954077388159821)
      ·
        refine ⟨1242288493107779020559933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3312769314954077388159821 1242288493107779020559933)
        ·
          refine ⟨465858184915417132709975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1242288493107779020559933 465858184915417132709975)
          ·
            refine ⟨698787277373125699064963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 465858184915417132709975 698787277373125699064963)
            ·
              refine ⟨1048180916059688548597445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 698787277373125699064963 1048180916059688548597445)
              ·
                refine ⟨196533921761191602862021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1048180916059688548597445 196533921761191602862021)
                ·
                  refine ⟨36850110330223425536629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196533921761191602862021 36850110330223425536629)
                  ·
                    rfl

theorem cell20_80736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 4, 4].length) (baseStart_80736 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80736 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80736 prefixEnd_80736 := by exact prefixLift 80736
  have htrace : WordTrace (prefixWord ++ tailWord_80736) baseStart_80736 baseEnd_80736 := by
    simpa [prefixWord, tailWord_80736, baseEnd_80736] using wordTrace_append hprefix tailTrace_80736
  have hstable : (prefixWord ++ tailWord_80736).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80736).length < 2 ^ (prefixWord ++ tailWord_80736).sum := by decide
  have hdescent : baseEnd_80736 < baseStart_80736 := by decide
  rcases family_descends (prefixWord ++ tailWord_80736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80739 : List Nat := [1, 1, 1, 5, 3, 3, 2, 4]
def baseStart_80739 : Nat := 118140960795 + 80739 * 2 ^ 59
def prefixEnd_80739 : Nat := 4983230072969 + 3 ^ 40 * 80739 * 2
def baseEnd_80739 : Nat := 12283826537322916145539

theorem tailTrace_80739 : CollatzResearch.WordTrace tailWord_80739 prefixEnd_80739 12283826537322916145539 := by
  unfold tailWord_80739
  simp only [CollatzResearch.WordTrace]
  refine ⟨2944793254503866968501271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1963195503002577979000847 2944793254503866968501271)
  ·
    refine ⟨4417189881755800452751907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2944793254503866968501271 4417189881755800452751907)
    ·
      refine ⟨6625784822633700679127861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4417189881755800452751907 6625784822633700679127861)
      ·
        refine ⟨621167327121909438668237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6625784822633700679127861 621167327121909438668237)
        ·
          refine ⟨232937747670716039500589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 621167327121909438668237 232937747670716039500589)
          ·
            refine ⟨87351655376518514812721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 232937747670716039500589 87351655376518514812721)
            ·
              refine ⟨65513741532388886109541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87351655376518514812721 65513741532388886109541)
              ·
                refine ⟨12283826537322916145539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65513741532388886109541 12283826537322916145539)
                ·
                  rfl

theorem cell20_80739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 3, 2, 4].length) (baseStart_80739 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80739 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80739 prefixEnd_80739 := by exact prefixLift 80739
  have htrace : WordTrace (prefixWord ++ tailWord_80739) baseStart_80739 baseEnd_80739 := by
    simpa [prefixWord, tailWord_80739, baseEnd_80739] using wordTrace_append hprefix tailTrace_80739
  have hstable : (prefixWord ++ tailWord_80739).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80739).length < 2 ^ (prefixWord ++ tailWord_80739).sum := by decide
  have hdescent : baseEnd_80739 < baseStart_80739 := by decide
  rcases family_descends (prefixWord ++ tailWord_80739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80766 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 4]
def baseStart_80766 : Nat := 118140960795 + 80766 * 2 ^ 59
def prefixEnd_80766 : Nat := 4983230072969 + 3 ^ 40 * 80766 * 2
def baseEnd_80766 : Nat := 36863803147676654536507

theorem tailTrace_80766 : CollatzResearch.WordTrace tailWord_80766 prefixEnd_80766 36863803147676654536507 := by
  unfold tailWord_80766
  simp only [CollatzResearch.WordTrace]
  refine ⟨368222253175756322466769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1963852016937367053156101 368222253175756322466769)
  ·
    refine ⟨276166689881817241850077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 368222253175756322466769 276166689881817241850077)
    ·
      refine ⟨103562508705681465693779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 276166689881817241850077 103562508705681465693779)
      ·
        refine ⟨155343763058522198540669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103562508705681465693779 155343763058522198540669)
        ·
          refine ⟨58253911146945824452751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 155343763058522198540669 58253911146945824452751)
          ·
            refine ⟨87380866720418736679127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58253911146945824452751 87380866720418736679127)
            ·
              refine ⟨131071300080628105018691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87380866720418736679127 131071300080628105018691)
              ·
                refine ⟨196606950120942157528037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131071300080628105018691 196606950120942157528037)
                ·
                  refine ⟨36863803147676654536507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 196606950120942157528037 36863803147676654536507)
                  ·
                    rfl

theorem cell20_80766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 4].length) (baseStart_80766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80766 prefixEnd_80766 := by exact prefixLift 80766
  have htrace : WordTrace (prefixWord ++ tailWord_80766) baseStart_80766 baseEnd_80766 := by
    simpa [prefixWord, tailWord_80766, baseEnd_80766] using wordTrace_append hprefix tailTrace_80766
  have hstable : (prefixWord ++ tailWord_80766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80766).length < 2 ^ (prefixWord ++ tailWord_80766).sum := by decide
  have hdescent : baseEnd_80766 < baseStart_80766 := by decide
  rcases family_descends (prefixWord ++ tailWord_80766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80825 : List Nat := [1, 2, 1, 4, 2, 4, 2, 2, 2]
def baseStart_80825 : Nat := 118140960795 + 80825 * 2 ^ 59
def prefixEnd_80825 : Nat := 4983230072969 + 3 ^ 40 * 80825 * 2
def baseEnd_80825 : Nat := 36890732355334671569599

theorem tailTrace_80825 : CollatzResearch.WordTrace tailWord_80825 prefixEnd_80825 36890732355334671569599 := by
  unfold tailWord_80825
  simp only [CollatzResearch.WordTrace]
  refine ⟨2947929932192303656131929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1965286621461535770754619 2947929932192303656131929)
  ·
    refine ⟨2210947449144227742098947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2947929932192303656131929 2210947449144227742098947)
    ·
      refine ⟨3316421173716341613148421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2210947449144227742098947 3316421173716341613148421)
      ·
        refine ⟨621828970071814052465329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3316421173716341613148421 621828970071814052465329)
        ·
          refine ⟨466371727553860539348997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 621828970071814052465329 466371727553860539348997)
          ·
            refine ⟨87444698916348851127937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 466371727553860539348997 87444698916348851127937)
            ·
              refine ⟨65583524187261638345953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87444698916348851127937 65583524187261638345953)
              ·
                refine ⟨49187643140446228759465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65583524187261638345953 49187643140446228759465)
                ·
                  refine ⟨36890732355334671569599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49187643140446228759465 36890732355334671569599)
                  ·
                    rfl

theorem cell20_80825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 2, 2, 2].length) (baseStart_80825 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80825 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80825 prefixEnd_80825 := by exact prefixLift 80825
  have htrace : WordTrace (prefixWord ++ tailWord_80825) baseStart_80825 baseEnd_80825 := by
    simpa [prefixWord, tailWord_80825, baseEnd_80825] using wordTrace_append hprefix tailTrace_80825
  have hstable : (prefixWord ++ tailWord_80825).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80825).length < 2 ^ (prefixWord ++ tailWord_80825).sum := by decide
  have hdescent : baseEnd_80825 < baseStart_80825 := by decide
  rcases family_descends (prefixWord ++ tailWord_80825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80843 : List Nat := [1, 1, 1, 1, 3, 5, 2, 3, 3]
def baseStart_80843 : Nat := 118140960795 + 80843 * 2 ^ 59
def prefixEnd_80843 : Nat := 4983230072969 + 3 ^ 40 * 80843 * 2
def baseEnd_80843 : Nat := 36898948045806608969525

theorem tailTrace_80843 : CollatzResearch.WordTrace tailWord_80843 prefixEnd_80843 36898948045806608969525 := by
  unfold tailWord_80843
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948586446127092730287183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1965724297418061820191455 2948586446127092730287183)
  ·
    refine ⟨4422879669190639095430775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2948586446127092730287183 4422879669190639095430775)
    ·
      refine ⟨6634319503785958643146163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4422879669190639095430775 6634319503785958643146163)
      ·
        refine ⟨9951479255678937964719245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6634319503785958643146163 9951479255678937964719245)
        ·
          refine ⟨3731804720879601736769717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9951479255678937964719245 3731804720879601736769717)
          ·
            refine ⟨349856692582462662822161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3731804720879601736769717 349856692582462662822161)
            ·
              refine ⟨262392519436846997116621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 349856692582462662822161 262392519436846997116621)
              ·
                refine ⟨98397194788817623918733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 262392519436846997116621 98397194788817623918733)
                ·
                  refine ⟨36898948045806608969525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98397194788817623918733 36898948045806608969525)
                  ·
                    rfl

theorem cell20_80843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 5, 2, 3, 3].length) (baseStart_80843 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80843 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80843 prefixEnd_80843 := by exact prefixLift 80843
  have htrace : WordTrace (prefixWord ++ tailWord_80843) baseStart_80843 baseEnd_80843 := by
    simpa [prefixWord, tailWord_80843, baseEnd_80843] using wordTrace_append hprefix tailTrace_80843
  have hstable : (prefixWord ++ tailWord_80843).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80843).length < 2 ^ (prefixWord ++ tailWord_80843).sum := by decide
  have hdescent : baseEnd_80843 < baseStart_80843 := by decide
  rcases family_descends (prefixWord ++ tailWord_80843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80853 : List Nat := [1, 3, 2, 3, 3, 1, 3, 4]
def baseStart_80853 : Nat := 118140960795 + 80853 * 2 ^ 59
def prefixEnd_80853 : Nat := 4983230072969 + 3 ^ 40 * 80853 * 2
def baseEnd_80853 : Nat := 12301170772763672878717

theorem tailTrace_80853 : CollatzResearch.WordTrace tailWord_80853 prefixEnd_80853 12301170772763672878717 := by
  unfold tailWord_80853
  simp only [CollatzResearch.WordTrace]
  refine ⟨2948951176090864438151213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1965967450727242958767475 2948951176090864438151213)
  ·
    refine ⟨1105856691034074164306705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2948951176090864438151213 1105856691034074164306705)
    ·
      refine ⟨829392518275555623230029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1105856691034074164306705 829392518275555623230029)
      ·
        refine ⟨311022194353333358711261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 829392518275555623230029 311022194353333358711261)
        ·
          refine ⟨116633322882500009516723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 311022194353333358711261 116633322882500009516723)
          ·
            refine ⟨174949984323750014275085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116633322882500009516723 174949984323750014275085)
            ·
              refine ⟨65606244121406255353157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 174949984323750014275085 65606244121406255353157)
              ·
                refine ⟨12301170772763672878717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65606244121406255353157 12301170772763672878717)
                ·
                  rfl

theorem cell20_80853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 1, 3, 4].length) (baseStart_80853 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80853 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80853 prefixEnd_80853 := by exact prefixLift 80853
  have htrace : WordTrace (prefixWord ++ tailWord_80853) baseStart_80853 baseEnd_80853 := by
    simpa [prefixWord, tailWord_80853, baseEnd_80853] using wordTrace_append hprefix tailTrace_80853
  have hstable : (prefixWord ++ tailWord_80853).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80853).length < 2 ^ (prefixWord ++ tailWord_80853).sum := by decide
  have hdescent : baseEnd_80853 < baseStart_80853 := by decide
  rcases family_descends (prefixWord ++ tailWord_80853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80881 : List Nat := [1, 2, 2, 2, 4, 2, 1, 1, 5]
def baseStart_80881 : Nat := 118140960795 + 80881 * 2 ^ 59
def prefixEnd_80881 : Nat := 4983230072969 + 3 ^ 40 * 80881 * 2
def baseEnd_80881 : Nat := 36916292281247365702703

theorem tailTrace_80881 : CollatzResearch.WordTrace tailWord_80881 prefixEnd_80881 36916292281247365702703 := by
  unfold tailWord_80881
  simp only [CollatzResearch.WordTrace]
  refine ⟨2949972419989425220170497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1966648279992950146780331 2949972419989425220170497)
  ·
    refine ⟨2212479314992068915127873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2949972419989425220170497 2212479314992068915127873)
    ·
      refine ⟨1659359486244051686345905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2212479314992068915127873 1659359486244051686345905)
      ·
        refine ⟨1244519614683038764759429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1659359486244051686345905 1244519614683038764759429)
        ·
          refine ⟨233347427753069768392393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1244519614683038764759429 233347427753069768392393)
          ·
            refine ⟨175010570814802326294295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233347427753069768392393 175010570814802326294295)
            ·
              refine ⟨262515856222203489441443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 175010570814802326294295 262515856222203489441443)
              ·
                refine ⟨393773784333305234162165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 262515856222203489441443 393773784333305234162165)
                ·
                  refine ⟨36916292281247365702703, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393773784333305234162165 36916292281247365702703)
                  ·
                    rfl

theorem cell20_80881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 1, 1, 5].length) (baseStart_80881 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80881 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80881 prefixEnd_80881 := by exact prefixLift 80881
  have htrace : WordTrace (prefixWord ++ tailWord_80881) baseStart_80881 baseEnd_80881 := by
    simpa [prefixWord, tailWord_80881, baseEnd_80881] using wordTrace_append hprefix tailTrace_80881
  have hstable : (prefixWord ++ tailWord_80881).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80881).length < 2 ^ (prefixWord ++ tailWord_80881).sum := by decide
  have hdescent : baseEnd_80881 < baseStart_80881 := by decide
  rcases family_descends (prefixWord ++ tailWord_80881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80894 : List Nat := [4, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_80894 : Nat := 118140960795 + 80894 * 2 ^ 59
def prefixEnd_80894 : Nat := 4983230072969 + 3 ^ 40 * 80894 * 2
def baseEnd_80894 : Nat := 36922225835477098269317

theorem tailTrace_80894 : CollatzResearch.WordTrace tailWord_80894 prefixEnd_80894 36922225835477098269317 := by
  unfold tailWord_80894
  simp only [CollatzResearch.WordTrace]
  refine ⟨368805821117791055049217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1966964379294885626929157 368805821117791055049217)
  ·
    refine ⟨276604365838343291286913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 368805821117791055049217 276604365838343291286913)
    ·
      refine ⟨207453274378757468465185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276604365838343291286913 207453274378757468465185)
      ·
        refine ⟨155589955784068101348889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207453274378757468465185 155589955784068101348889)
        ·
          refine ⟨116692466838051076011667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 155589955784068101348889 116692466838051076011667)
          ·
            refine ⟨175038700257076614017501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 116692466838051076011667 175038700257076614017501)
            ·
              refine ⟨65639512596403730256563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175038700257076614017501 65639512596403730256563)
              ·
                refine ⟨98459268894605595384845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65639512596403730256563 98459268894605595384845)
                ·
                  refine ⟨36922225835477098269317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98459268894605595384845 36922225835477098269317)
                  ·
                    rfl

theorem cell20_80894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_80894 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80894 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80894 prefixEnd_80894 := by exact prefixLift 80894
  have htrace : WordTrace (prefixWord ++ tailWord_80894) baseStart_80894 baseEnd_80894 := by
    simpa [prefixWord, tailWord_80894, baseEnd_80894] using wordTrace_append hprefix tailTrace_80894
  have hstable : (prefixWord ++ tailWord_80894).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80894).length < 2 ^ (prefixWord ++ tailWord_80894).sum := by decide
  have hdescent : baseEnd_80894 < baseStart_80894 := by decide
  rcases family_descends (prefixWord ++ tailWord_80894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80914 : List Nat := [3, 2, 5, 1, 2, 1, 1, 3, 2]
def baseStart_80914 : Nat := 118140960795 + 80914 * 2 ^ 59
def prefixEnd_80914 : Nat := 4983230072969 + 3 ^ 40 * 80914 * 2
def baseEnd_80914 : Nat := 36931354380445917602569

theorem tailTrace_80914 : CollatzResearch.WordTrace tailWord_80914 prefixEnd_80914 36931354380445917602569 := by
  unfold tailWord_80914
  simp only [CollatzResearch.WordTrace]
  refine ⟨737794007217467964030449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1967450685913247904081197 737794007217467964030449)
  ·
    refine ⟨553345505413100973022837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 737794007217467964030449 553345505413100973022837)
    ·
      refine ⟨51876141132478216220891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 553345505413100973022837 51876141132478216220891)
      ·
        refine ⟨77814211698717324331337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51876141132478216220891 77814211698717324331337)
        ·
          refine ⟨58360658774037993248503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77814211698717324331337 58360658774037993248503)
          ·
            refine ⟨87540988161056989872755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58360658774037993248503 87540988161056989872755)
            ·
              refine ⟨131311482241585484809133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87540988161056989872755 131311482241585484809133)
              ·
                refine ⟨49241805840594556803425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 131311482241585484809133 49241805840594556803425)
                ·
                  refine ⟨36931354380445917602569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49241805840594556803425 36931354380445917602569)
                  ·
                    rfl

theorem cell20_80914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 5, 1, 2, 1, 1, 3, 2].length) (baseStart_80914 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80914 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80914 prefixEnd_80914 := by exact prefixLift 80914
  have htrace : WordTrace (prefixWord ++ tailWord_80914) baseStart_80914 baseEnd_80914 := by
    simpa [prefixWord, tailWord_80914, baseEnd_80914] using wordTrace_append hprefix tailTrace_80914
  have hstable : (prefixWord ++ tailWord_80914).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80914).length < 2 ^ (prefixWord ++ tailWord_80914).sum := by decide
  have hdescent : baseEnd_80914 < baseStart_80914 := by decide
  rcases family_descends (prefixWord ++ tailWord_80914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80919 : List Nat := [1, 1, 3, 5, 1, 1, 1, 2, 5]
def baseStart_80919 : Nat := 118140960795 + 80919 * 2 ^ 59
def prefixEnd_80919 : Nat := 4983230072969 + 3 ^ 40 * 80919 * 2
def baseEnd_80919 : Nat := 36933636516688122435881

theorem tailTrace_80919 : CollatzResearch.WordTrace tailWord_80919 prefixEnd_80919 36933636516688122435881 := by
  unfold tailWord_80919
  simp only [CollatzResearch.WordTrace]
  refine ⟨2951358393851757710053811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1967572262567838473369207 2951358393851757710053811)
  ·
    refine ⟨4427037590777636565080717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2951358393851757710053811 4427037590777636565080717)
    ·
      refine ⟨1660139096541613711905269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4427037590777636565080717 1660139096541613711905269)
      ·
        refine ⟨155638040300776285491119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1660139096541613711905269 155638040300776285491119)
        ·
          refine ⟨233457060451164428236679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155638040300776285491119 233457060451164428236679)
          ·
            refine ⟨350185590676746642355019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233457060451164428236679 350185590676746642355019)
            ·
              refine ⟨525278386015119963532529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350185590676746642355019 525278386015119963532529)
              ·
                refine ⟨393958789511339972649397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 525278386015119963532529 393958789511339972649397)
                ·
                  refine ⟨36933636516688122435881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 393958789511339972649397 36933636516688122435881)
                  ·
                    rfl

theorem cell20_80919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 1, 2, 5].length) (baseStart_80919 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80919 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80919 prefixEnd_80919 := by exact prefixLift 80919
  have htrace : WordTrace (prefixWord ++ tailWord_80919) baseStart_80919 baseEnd_80919 := by
    simpa [prefixWord, tailWord_80919, baseEnd_80919] using wordTrace_append hprefix tailTrace_80919
  have hstable : (prefixWord ++ tailWord_80919).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80919).length < 2 ^ (prefixWord ++ tailWord_80919).sum := by decide
  have hdescent : baseEnd_80919 < baseStart_80919 := by decide
  rcases family_descends (prefixWord ++ tailWord_80919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80940 : List Nat := [2, 2, 1, 1, 1, 2, 3, 3, 5]
def baseStart_80940 : Nat := 118140960795 + 80940 * 2 ^ 59
def prefixEnd_80940 : Nat := 4983230072969 + 3 ^ 40 * 80940 * 2
def baseEnd_80940 : Nat := 36943221488905382735795

theorem tailTrace_80940 : CollatzResearch.WordTrace tailWord_80940 prefixEnd_80940 36943221488905382735795 := by
  unfold tailWord_80940
  simp only [CollatzResearch.WordTrace]
  refine ⟨1476062163387839148284137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1968082884517118864378849 1476062163387839148284137)
  ·
    refine ⟨1107046622540879361213103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1476062163387839148284137 1107046622540879361213103)
    ·
      refine ⟨1660569933811319041819655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1107046622540879361213103 1660569933811319041819655)
      ·
        refine ⟨2490854900716978562729483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1660569933811319041819655 2490854900716978562729483)
        ·
          refine ⟨3736282351075467844094225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2490854900716978562729483 3736282351075467844094225)
          ·
            refine ⟨2802211763306600883070669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3736282351075467844094225 2802211763306600883070669)
            ·
              refine ⟨1050829411239975331151501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2802211763306600883070669 1050829411239975331151501)
              ·
                refine ⟨394061029214990749181813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1050829411239975331151501 394061029214990749181813)
                ·
                  refine ⟨36943221488905382735795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394061029214990749181813 36943221488905382735795)
                  ·
                    rfl

theorem cell20_80940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_80940 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80940 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80940 prefixEnd_80940 := by exact prefixLift 80940
  have htrace : WordTrace (prefixWord ++ tailWord_80940) baseStart_80940 baseEnd_80940 := by
    simpa [prefixWord, tailWord_80940, baseEnd_80940] using wordTrace_append hprefix tailTrace_80940
  have hstable : (prefixWord ++ tailWord_80940).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80940).length < 2 ^ (prefixWord ++ tailWord_80940).sum := by decide
  have hdescent : baseEnd_80940 < baseStart_80940 := by decide
  rcases family_descends (prefixWord ++ tailWord_80940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80950 : List Nat := [5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_80950 : Nat := 118140960795 + 80950 * 2 ^ 59
def prefixEnd_80950 : Nat := 4983230072969 + 3 ^ 40 * 80950 * 2
def baseEnd_80950 : Nat := 12315928587129930800807

theorem tailTrace_80950 : CollatzResearch.WordTrace tailWord_80950 prefixEnd_80950 12315928587129930800807 := by
  unfold tailWord_80950
  simp only [CollatzResearch.WordTrace]
  refine ⟨184530566046215625277019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 1968326037826300002954869 184530566046215625277019)
  ·
    refine ⟨276795849069323437915529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 184530566046215625277019 276795849069323437915529)
    ·
      refine ⟨207596886801992578436647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276795849069323437915529 207596886801992578436647)
      ·
        refine ⟨311395330202988867654971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 207596886801992578436647 311395330202988867654971)
        ·
          refine ⟨467092995304483301482457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311395330202988867654971 467092995304483301482457)
          ·
            refine ⟨350319746478362476111843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 467092995304483301482457 350319746478362476111843)
            ·
              refine ⟨525479619717543714167765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 350319746478362476111843 525479619717543714167765)
              ·
                refine ⟨12315928587129930800807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 525479619717543714167765 12315928587129930800807)
                ·
                  rfl

theorem cell20_80950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_80950 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80950 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80950 prefixEnd_80950 := by exact prefixLift 80950
  have htrace : WordTrace (prefixWord ++ tailWord_80950) baseStart_80950 baseEnd_80950 := by
    simpa [prefixWord, tailWord_80950, baseEnd_80950] using wordTrace_append hprefix tailTrace_80950
  have hstable : (prefixWord ++ tailWord_80950).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80950).length < 2 ^ (prefixWord ++ tailWord_80950).sum := by decide
  have hdescent : baseEnd_80950 < baseStart_80950 := by decide
  rcases family_descends (prefixWord ++ tailWord_80950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80953 : List Nat := [1, 2, 1, 5, 2, 3, 2, 1, 3]
def baseStart_80953 : Nat := 118140960795 + 80953 * 2 ^ 59
def prefixEnd_80953 : Nat := 4983230072969 + 3 ^ 40 * 80953 * 2
def baseEnd_80953 : Nat := 36949155043135115302409

theorem tailTrace_80953 : CollatzResearch.WordTrace tailWord_80953 prefixEnd_80953 36949155043135115302409 := by
  unfold tailWord_80953
  simp only [CollatzResearch.WordTrace]
  refine ⟨2952598475728581516791513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1968398983819054344527675 2952598475728581516791513)
  ·
    refine ⟨2214448856796436137593635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2952598475728581516791513 2214448856796436137593635)
    ·
      refine ⟨3321673285194654206390453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2214448856796436137593635 3321673285194654206390453)
      ·
        refine ⟨311406870486998831849105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3321673285194654206390453 311406870486998831849105)
        ·
          refine ⟨233555152865249123886829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 311406870486998831849105 233555152865249123886829)
          ·
            refine ⟨87583182324468421457561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233555152865249123886829 87583182324468421457561)
            ·
              refine ⟨65687386743351316093171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87583182324468421457561 65687386743351316093171)
              ·
                refine ⟨98531080115026974139757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65687386743351316093171 98531080115026974139757)
                ·
                  refine ⟨36949155043135115302409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98531080115026974139757 36949155043135115302409)
                  ·
                    rfl

theorem cell20_80953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 3, 2, 1, 3].length) (baseStart_80953 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80953 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80953 prefixEnd_80953 := by exact prefixLift 80953
  have htrace : WordTrace (prefixWord ++ tailWord_80953) baseStart_80953 baseEnd_80953 := by
    simpa [prefixWord, tailWord_80953, baseEnd_80953] using wordTrace_append hprefix tailTrace_80953
  have hstable : (prefixWord ++ tailWord_80953).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80953).length < 2 ^ (prefixWord ++ tailWord_80953).sum := by decide
  have hdescent : baseEnd_80953 < baseStart_80953 := by decide
  rcases family_descends (prefixWord ++ tailWord_80953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80981 : List Nat := [1, 3, 2, 2, 1, 2, 2, 5, 2]
def baseStart_80981 : Nat := 118140960795 + 80981 * 2 ^ 59
def prefixEnd_80981 : Nat := 4983230072969 + 3 ^ 40 * 80981 * 2
def baseEnd_80981 : Nat := 36961935006091462368961

theorem tailTrace_80981 : CollatzResearch.WordTrace tailWord_80981 prefixEnd_80981 36961935006091462368961 := by
  unfold tailWord_80981
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953619719627142298810797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1969079813084761532540531 2953619719627142298810797)
  ·
    refine ⟨1107607394860178362054049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2953619719627142298810797 1107607394860178362054049)
    ·
      refine ⟨830705546145133771540537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1107607394860178362054049 830705546145133771540537)
      ·
        refine ⟨623029159608850328655403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 830705546145133771540537 623029159608850328655403)
        ·
          refine ⟨934543739413275492983105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 623029159608850328655403 934543739413275492983105)
          ·
            refine ⟨700907804559956619737329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 934543739413275492983105 700907804559956619737329)
            ·
              refine ⟨525680853419967464802997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 700907804559956619737329 525680853419967464802997)
              ·
                refine ⟨49282580008121949825281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 525680853419967464802997 49282580008121949825281)
                ·
                  refine ⟨36961935006091462368961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49282580008121949825281 36961935006091462368961)
                  ·
                    rfl

theorem cell20_80981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 5, 2].length) (baseStart_80981 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80981 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80981 prefixEnd_80981 := by exact prefixLift 80981
  have htrace : WordTrace (prefixWord ++ tailWord_80981) baseStart_80981 baseEnd_80981 := by
    simpa [prefixWord, tailWord_80981, baseEnd_80981] using wordTrace_append hprefix tailTrace_80981
  have hstable : (prefixWord ++ tailWord_80981).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80981).length < 2 ^ (prefixWord ++ tailWord_80981).sum := by decide
  have hdescent : baseEnd_80981 < baseStart_80981 := by decide
  rcases family_descends (prefixWord ++ tailWord_80981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80985 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 8]
def baseStart_80985 : Nat := 118140960795 + 80985 * 2 ^ 59
def prefixEnd_80985 : Nat := 4983230072969 + 3 ^ 40 * 80985 * 2
def baseEnd_80985 : Nat := 36963760715085226235611

theorem tailTrace_80985 : CollatzResearch.WordTrace tailWord_80985 prefixEnd_80985 36963760715085226235611 := by
  unfold tailWord_80985
  simp only [CollatzResearch.WordTrace]
  refine ⟨2953765611612650981956409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1969177074408433987970939 2953765611612650981956409)
  ·
    refine ⟨2215324208709488236467307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2953765611612650981956409 2215324208709488236467307)
    ·
      refine ⟨3322986313064232354700961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2215324208709488236467307 3322986313064232354700961)
      ·
        refine ⟨2492239734798174266025721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3322986313064232354700961 2492239734798174266025721)
        ·
          refine ⟨1869179801098630699519291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2492239734798174266025721 1869179801098630699519291)
          ·
            refine ⟨2803769701647946049278937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1869179801098630699519291 2803769701647946049278937)
            ·
              refine ⟨2102827276235959536959203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2803769701647946049278937 2102827276235959536959203)
              ·
                refine ⟨3154240914353939305438805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2102827276235959536959203 3154240914353939305438805)
                ·
                  refine ⟨36963760715085226235611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3154240914353939305438805 36963760715085226235611)
                  ·
                    rfl

theorem cell20_80985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 8].length) (baseStart_80985 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80985 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80985 prefixEnd_80985 := by exact prefixLift 80985
  have htrace : WordTrace (prefixWord ++ tailWord_80985) baseStart_80985 baseEnd_80985 := by
    simpa [prefixWord, tailWord_80985, baseEnd_80985] using wordTrace_append hprefix tailTrace_80985
  have hstable : (prefixWord ++ tailWord_80985).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80985).length < 2 ^ (prefixWord ++ tailWord_80985).sum := by decide
  have hdescent : baseEnd_80985 < baseStart_80985 := by decide
  rcases family_descends (prefixWord ++ tailWord_80985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_80994 : List Nat := [3, 3, 2, 2, 1, 3, 2, 2, 2]
def baseStart_80994 : Nat := 118140960795 + 80994 * 2 ^ 59
def prefixEnd_80994 : Nat := 4983230072969 + 3 ^ 40 * 80994 * 2
def baseEnd_80994 : Nat := 36967868560321194935575

theorem tailTrace_80994 : CollatzResearch.WordTrace tailWord_80994 prefixEnd_80994 36967868560321194935575 := by
  unfold tailWord_80994
  simp only [CollatzResearch.WordTrace]
  refine ⟨738523467145011379758509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1969395912386697012689357 738523467145011379758509)
  ·
    refine ⟨276946300179379267409441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 738523467145011379758509 276946300179379267409441)
    ·
      refine ⟨207709725134534450557081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 276946300179379267409441 207709725134534450557081)
      ·
        refine ⟨155782293850900837917811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 207709725134534450557081 155782293850900837917811)
        ·
          refine ⟨233673440776351256876717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155782293850900837917811 233673440776351256876717)
          ·
            refine ⟨87627540291131721328769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 233673440776351256876717 87627540291131721328769)
            ·
              refine ⟨65720655218348790996577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 87627540291131721328769 65720655218348790996577)
              ·
                refine ⟨49290491413761593247433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65720655218348790996577 49290491413761593247433)
                ·
                  refine ⟨36967868560321194935575, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49290491413761593247433 36967868560321194935575)
                  ·
                    rfl

theorem cell20_80994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 3, 2, 2, 2].length) (baseStart_80994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_80994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_80994 prefixEnd_80994 := by exact prefixLift 80994
  have htrace : WordTrace (prefixWord ++ tailWord_80994) baseStart_80994 baseEnd_80994 := by
    simpa [prefixWord, tailWord_80994, baseEnd_80994] using wordTrace_append hprefix tailTrace_80994
  have hstable : (prefixWord ++ tailWord_80994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_80994).length < 2 ^ (prefixWord ++ tailWord_80994).sum := by decide
  have hdescent : baseEnd_80994 < baseStart_80994 := by decide
  rcases family_descends (prefixWord ++ tailWord_80994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81047 : List Nat := [1, 1, 3, 3, 3, 2, 7]
def baseStart_81047 : Nat := 118140960795 + 81047 * 2 ^ 59
def prefixEnd_81047 : Nat := 4983230072969 + 3 ^ 40 * 81047 * 2
def baseEnd_81047 : Nat := 4110228800498729574299

theorem tailTrace_81047 : CollatzResearch.WordTrace tailWord_81047 prefixEnd_81047 4110228800498729574299 := by
  unfold tailWord_81047
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956026937388035570713395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1970684624925357047142263 2956026937388035570713395)
  ·
    refine ⟨4434040406082053356070093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2956026937388035570713395 4434040406082053356070093)
    ·
      refine ⟨1662765152280770008526285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4434040406082053356070093 1662765152280770008526285)
      ·
        refine ⟨623536932105288753197357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1662765152280770008526285 623536932105288753197357)
        ·
          refine ⟨233826349539483282449009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 623536932105288753197357 233826349539483282449009)
          ·
            refine ⟨175369762154612461836757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 233826349539483282449009 175369762154612461836757)
            ·
              refine ⟨4110228800498729574299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 175369762154612461836757 4110228800498729574299)
              ·
                rfl

theorem cell20_81047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 2, 7].length) (baseStart_81047 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81047 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81047 prefixEnd_81047 := by exact prefixLift 81047
  have htrace : WordTrace (prefixWord ++ tailWord_81047) baseStart_81047 baseEnd_81047 := by
    simpa [prefixWord, tailWord_81047, baseEnd_81047] using wordTrace_append hprefix tailTrace_81047
  have hstable : (prefixWord ++ tailWord_81047).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81047).length < 2 ^ (prefixWord ++ tailWord_81047).sum := by decide
  have hdescent : baseEnd_81047 < baseStart_81047 := by decide
  rcases family_descends (prefixWord ++ tailWord_81047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81050 : List Nat := [3, 1, 1, 5, 1, 1, 3, 2, 3]
def baseStart_81050 : Nat := 118140960795 + 81050 * 2 ^ 59
def prefixEnd_81050 : Nat := 4983230072969 + 3 ^ 40 * 81050 * 2
def baseEnd_81050 : Nat := 36993428486233889068679

theorem tailTrace_81050 : CollatzResearch.WordTrace tailWord_81050 prefixEnd_81050 36993428486233889068679 := by
  unfold tailWord_81050
  simp only [CollatzResearch.WordTrace]
  refine ⟨739034089094291770768151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1970757570918111388715069 739034089094291770768151)
  ·
    refine ⟨1108551133641437656152227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 739034089094291770768151 1108551133641437656152227)
    ·
      refine ⟨1662826700462156484228341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1108551133641437656152227 1662826700462156484228341)
      ·
        refine ⟨155890003168327170396407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1662826700462156484228341 155890003168327170396407)
        ·
          refine ⟨233835004752490755594611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 155890003168327170396407 233835004752490755594611)
          ·
            refine ⟨350752507128736133391917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 233835004752490755594611 350752507128736133391917)
            ·
              refine ⟨131532190173276050021969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 350752507128736133391917 131532190173276050021969)
              ·
                refine ⟨98649142629957037516477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131532190173276050021969 98649142629957037516477)
                ·
                  refine ⟨36993428486233889068679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98649142629957037516477 36993428486233889068679)
                  ·
                    rfl

theorem cell20_81050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 1, 3, 2, 3].length) (baseStart_81050 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81050 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81050 prefixEnd_81050 := by exact prefixLift 81050
  have htrace : WordTrace (prefixWord ++ tailWord_81050) baseStart_81050 baseEnd_81050 := by
    simpa [prefixWord, tailWord_81050, baseEnd_81050] using wordTrace_append hprefix tailTrace_81050
  have hstable : (prefixWord ++ tailWord_81050).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81050).length < 2 ^ (prefixWord ++ tailWord_81050).sum := by decide
  have hdescent : baseEnd_81050 < baseStart_81050 := by decide
  rcases family_descends (prefixWord ++ tailWord_81050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81057 : List Nat := [1, 2, 3, 3, 1, 1, 1, 6, 2]
def baseStart_81057 : Nat := 118140960795 + 81057 * 2 ^ 59
def prefixEnd_81057 : Nat := 4983230072969 + 3 ^ 40 * 81057 * 2
def baseEnd_81057 : Nat := 36996623476972975835317

theorem tailTrace_81057 : CollatzResearch.WordTrace tailWord_81057 prefixEnd_81057 36996623476972975835317 := by
  unfold tailWord_81057
  simp only [CollatzResearch.WordTrace]
  refine ⟨2956391667351807278577425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1970927778234538185718283 2956391667351807278577425)
  ·
    refine ⟨2217293750513855458933069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2956391667351807278577425 2217293750513855458933069)
    ·
      refine ⟨831485156442695797099901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2217293750513855458933069 831485156442695797099901)
      ·
        refine ⟨311806933666010923912463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 831485156442695797099901 311806933666010923912463)
        ·
          refine ⟨467710400499016385868695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 311806933666010923912463 467710400499016385868695)
          ·
            refine ⟨701565600748524578803043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 467710400499016385868695 701565600748524578803043)
            ·
              refine ⟨1052348401122786868204565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 701565600748524578803043 1052348401122786868204565)
              ·
                refine ⟨49328831302630634447089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1052348401122786868204565 49328831302630634447089)
                ·
                  refine ⟨36996623476972975835317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49328831302630634447089 36996623476972975835317)
                  ·
                    rfl

theorem cell20_81057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 1, 6, 2].length) (baseStart_81057 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81057 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81057 prefixEnd_81057 := by exact prefixLift 81057
  have htrace : WordTrace (prefixWord ++ tailWord_81057) baseStart_81057 baseEnd_81057 := by
    simpa [prefixWord, tailWord_81057, baseEnd_81057] using wordTrace_append hprefix tailTrace_81057
  have hstable : (prefixWord ++ tailWord_81057).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81057).length < 2 ^ (prefixWord ++ tailWord_81057).sum := by decide
  have hdescent : baseEnd_81057 < baseStart_81057 := by decide
  rcases family_descends (prefixWord ++ tailWord_81057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81102 : List Nat := [4, 1, 1, 1, 5, 2, 6]
def baseStart_81102 : Nat := 118140960795 + 81102 * 2 ^ 59
def prefixEnd_81102 : Nat := 4983230072969 + 3 ^ 40 * 81102 * 2
def baseEnd_81102 : Nat := 4113018078128091037237

theorem tailTrace_81102 : CollatzResearch.WordTrace tailWord_81102 prefixEnd_81102 4113018078128091037237 := by
  unfold tailWord_81102
  simp only [CollatzResearch.WordTrace]
  refine ⟨369754119023597495495695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1972021968125853309310373 369754119023597495495695)
  ·
    refine ⟨554631178535396243243543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 369754119023597495495695 554631178535396243243543)
    ·
      refine ⟨831946767803094364865315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 554631178535396243243543 831946767803094364865315)
      ·
        refine ⟨1247920151704641547297973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 831946767803094364865315 1247920151704641547297973)
        ·
          refine ⟨116992514222310145059185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1247920151704641547297973 116992514222310145059185)
          ·
            refine ⟨87744385666732608794389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 116992514222310145059185 87744385666732608794389)
            ·
              refine ⟨4113018078128091037237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 87744385666732608794389 4113018078128091037237)
              ·
                rfl

theorem cell20_81102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 5, 2, 6].length) (baseStart_81102 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81102 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81102 prefixEnd_81102 := by exact prefixLift 81102
  have htrace : WordTrace (prefixWord ++ tailWord_81102) baseStart_81102 baseEnd_81102 := by
    simpa [prefixWord, tailWord_81102, baseEnd_81102] using wordTrace_append hprefix tailTrace_81102
  have hstable : (prefixWord ++ tailWord_81102).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81102).length < 2 ^ (prefixWord ++ tailWord_81102).sum := by decide
  have hdescent : baseEnd_81102 < baseStart_81102 := by decide
  rcases family_descends (prefixWord ++ tailWord_81102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81108 : List Nat := [2, 4, 1, 4, 1, 1, 3, 2, 2]
def baseStart_81108 : Nat := 118140960795 + 81108 * 2 ^ 59
def prefixEnd_81108 : Nat := 4983230072969 + 3 ^ 40 * 81108 * 2
def baseEnd_81108 : Nat := 37019901266643465135109

theorem tailTrace_81108 : CollatzResearch.WordTrace tailWord_81108 prefixEnd_81108 37019901266643465135109 := by
  unfold tailWord_81108
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479125895083521494341989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1972167860111361992455985 1479125895083521494341989)
  ·
    refine ⟨277336105328160280189123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1479125895083521494341989 277336105328160280189123)
    ·
      refine ⟨416004157992240420283685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 277336105328160280189123 416004157992240420283685)
      ·
        refine ⟨78000779623545078803191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 416004157992240420283685 78000779623545078803191)
        ·
          refine ⟨117001169435317618204787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 78000779623545078803191 117001169435317618204787)
          ·
            refine ⟨175501754152976427307181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117001169435317618204787 175501754152976427307181)
            ·
              refine ⟨65813157807366160240193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175501754152976427307181 65813157807366160240193)
              ·
                refine ⟨49359868355524620180145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65813157807366160240193 49359868355524620180145)
                ·
                  refine ⟨37019901266643465135109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49359868355524620180145 37019901266643465135109)
                  ·
                    rfl

theorem cell20_81108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_81108 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81108 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81108 prefixEnd_81108 := by exact prefixLift 81108
  have htrace : WordTrace (prefixWord ++ tailWord_81108) baseStart_81108 baseEnd_81108 := by
    simpa [prefixWord, tailWord_81108, baseEnd_81108] using wordTrace_append hprefix tailTrace_81108
  have hstable : (prefixWord ++ tailWord_81108).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81108).length < 2 ^ (prefixWord ++ tailWord_81108).sum := by decide
  have hdescent : baseEnd_81108 < baseStart_81108 := by decide
  rcases family_descends (prefixWord ++ tailWord_81108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81109 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 5]
def baseStart_81109 : Nat := 118140960795 + 81109 * 2 ^ 59
def prefixEnd_81109 : Nat := 4983230072969 + 3 ^ 40 * 81109 * 2
def baseEnd_81109 : Nat := 37020357693891906101771

theorem tailTrace_81109 : CollatzResearch.WordTrace tailWord_81109 prefixEnd_81109 37020357693891906101771 := by
  unfold tailWord_81109
  simp only [CollatzResearch.WordTrace]
  refine ⟨2958288263163420159470381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1972192175442280106313587 2958288263163420159470381)
  ·
    refine ⟨1109358098686282559801393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2958288263163420159470381 1109358098686282559801393)
    ·
      refine ⟨832018574014711919851045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1109358098686282559801393 832018574014711919851045)
      ·
        refine ⟨156003482627758484972071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 832018574014711919851045 156003482627758484972071)
        ·
          refine ⟨234005223941637727458107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 156003482627758484972071 234005223941637727458107)
          ·
            refine ⟨351007835912456591187161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234005223941637727458107 351007835912456591187161)
            ·
              refine ⟨263255876934342443390371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 351007835912456591187161 263255876934342443390371)
              ·
                refine ⟨394883815401513665085557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 263255876934342443390371 394883815401513665085557)
                ·
                  refine ⟨37020357693891906101771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 394883815401513665085557 37020357693891906101771)
                  ·
                    rfl

theorem cell20_81109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 5].length) (baseStart_81109 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81109 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81109 prefixEnd_81109 := by exact prefixLift 81109
  have htrace : WordTrace (prefixWord ++ tailWord_81109) baseStart_81109 baseEnd_81109 := by
    simpa [prefixWord, tailWord_81109, baseEnd_81109] using wordTrace_append hprefix tailTrace_81109
  have hstable : (prefixWord ++ tailWord_81109).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81109).length < 2 ^ (prefixWord ++ tailWord_81109).sum := by decide
  have hdescent : baseEnd_81109 < baseStart_81109 := by decide
  rcases family_descends (prefixWord ++ tailWord_81109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81112 : List Nat := [2, 1, 2, 2, 6, 1, 1, 1, 4]
def baseStart_81112 : Nat := 118140960795 + 81112 * 2 ^ 59
def prefixEnd_81112 : Nat := 4983230072969 + 3 ^ 40 * 81112 * 2
def baseEnd_81112 : Nat := 37021726975637229001759

theorem tailTrace_81112 : CollatzResearch.WordTrace tailWord_81112 prefixEnd_81112 37021726975637229001759 := by
  unfold tailWord_81112
  simp only [CollatzResearch.WordTrace]
  refine ⟨1479198841076275835914795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1972265121435034447886393 1479198841076275835914795)
  ·
    refine ⟨2218798261614413753872193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1479198841076275835914795 2218798261614413753872193)
    ·
      refine ⟨1664098696210810315404145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2218798261614413753872193 1664098696210810315404145)
      ·
        refine ⟨1248074022158107736553109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664098696210810315404145 1248074022158107736553109)
        ·
          refine ⟨58503469788661300150927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 1248074022158107736553109 58503469788661300150927)
          ·
            refine ⟨87755204682991950226391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 58503469788661300150927 87755204682991950226391)
            ·
              refine ⟨131632807024487925339587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87755204682991950226391 131632807024487925339587)
              ·
                refine ⟨197449210536731888009381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131632807024487925339587 197449210536731888009381)
                ·
                  refine ⟨37021726975637229001759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197449210536731888009381 37021726975637229001759)
                  ·
                    rfl

theorem cell20_81112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 6, 1, 1, 1, 4].length) (baseStart_81112 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81112 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81112 prefixEnd_81112 := by exact prefixLift 81112
  have htrace : WordTrace (prefixWord ++ tailWord_81112) baseStart_81112 baseEnd_81112 := by
    simpa [prefixWord, tailWord_81112, baseEnd_81112] using wordTrace_append hprefix tailTrace_81112
  have hstable : (prefixWord ++ tailWord_81112).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81112).length < 2 ^ (prefixWord ++ tailWord_81112).sum := by decide
  have hdescent : baseEnd_81112 < baseStart_81112 := by decide
  rcases family_descends (prefixWord ++ tailWord_81112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81137 : List Nat := [1, 2, 2, 2, 2, 1, 1, 3, 6]
def baseStart_81137 : Nat := 118140960795 + 81137 * 2 ^ 59
def prefixEnd_81137 : Nat := 4983230072969 + 3 ^ 40 * 81137 * 2
def baseEnd_81137 : Nat := 37033137656848253168323

theorem tailTrace_81137 : CollatzResearch.WordTrace tailWord_81137 prefixEnd_81137 37033137656848253168323 := by
  unfold tailWord_81137
  simp only [CollatzResearch.WordTrace]
  refine ⟨2959309507061980941489665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1972873004707987294326443 2959309507061980941489665)
  ·
    refine ⟨2219482130296485706117249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2959309507061980941489665 2219482130296485706117249)
    ·
      refine ⟨1664611597722364279587937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2219482130296485706117249 1664611597722364279587937)
      ·
        refine ⟨1248458698291773209690953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1664611597722364279587937 1248458698291773209690953)
        ·
          refine ⟨936344023718829907268215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1248458698291773209690953 936344023718829907268215)
          ·
            refine ⟨1404516035578244860902323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 936344023718829907268215 1404516035578244860902323)
            ·
              refine ⟨2106774053367367291353485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1404516035578244860902323 2106774053367367291353485)
              ·
                refine ⟨790040270012762734257557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2106774053367367291353485 790040270012762734257557)
                ·
                  refine ⟨37033137656848253168323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 790040270012762734257557 37033137656848253168323)
                  ·
                    rfl

theorem cell20_81137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 3, 6].length) (baseStart_81137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81137 prefixEnd_81137 := by exact prefixLift 81137
  have htrace : WordTrace (prefixWord ++ tailWord_81137) baseStart_81137 baseEnd_81137 := by
    simpa [prefixWord, tailWord_81137, baseEnd_81137] using wordTrace_append hprefix tailTrace_81137
  have hstable : (prefixWord ++ tailWord_81137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81137).length < 2 ^ (prefixWord ++ tailWord_81137).sum := by decide
  have hdescent : baseEnd_81137 < baseStart_81137 := by decide
  rcases family_descends (prefixWord ++ tailWord_81137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81178 : List Nat := [3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_81178 : Nat := 118140960795 + 81178 * 2 ^ 59
def prefixEnd_81178 : Nat := 4983230072969 + 3 ^ 40 * 81178 * 2
def baseEnd_81178 : Nat := 12350617058011444267163

theorem tailTrace_81178 : CollatzResearch.WordTrace tailWord_81178 prefixEnd_81178 12350617058011444267163 := by
  unfold tailWord_81178
  simp only [CollatzResearch.WordTrace]
  refine ⟨740201224978361235933047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1973869933275629962488125 740201224978361235933047)
  ·
    refine ⟨1110301837467541853899571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 740201224978361235933047 1110301837467541853899571)
    ·
      refine ⟨1665452756201312780849357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1110301837467541853899571 1665452756201312780849357)
      ·
        refine ⟨624544783575492292818509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1665452756201312780849357 624544783575492292818509)
        ·
          refine ⟨234204293840809609806941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 624544783575492292818509 234204293840809609806941)
          ·
            refine ⟨87826610190303603677603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 234204293840809609806941 87826610190303603677603)
            ·
              refine ⟨131739915285455405516405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 87826610190303603677603 131739915285455405516405)
              ·
                refine ⟨12350617058011444267163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 131739915285455405516405 12350617058011444267163)
                ·
                  rfl

theorem cell20_81178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_81178 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81178 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81178 prefixEnd_81178 := by exact prefixLift 81178
  have htrace : WordTrace (prefixWord ++ tailWord_81178) baseStart_81178 baseEnd_81178 := by
    simpa [prefixWord, tailWord_81178, baseEnd_81178] using wordTrace_append hprefix tailTrace_81178
  have hstable : (prefixWord ++ tailWord_81178).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81178).length < 2 ^ (prefixWord ++ tailWord_81178).sum := by decide
  have hdescent : baseEnd_81178 < baseStart_81178 := by decide
  rcases family_descends (prefixWord ++ tailWord_81178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81192 : List Nat := [2, 1, 5, 1, 2, 1, 1, 1, 6]
def baseStart_81192 : Nat := 118140960795 + 81192 * 2 ^ 59
def prefixEnd_81192 : Nat := 4983230072969 + 3 ^ 40 * 81192 * 2
def baseEnd_81192 : Nat := 37058241155512506334765

theorem tailTrace_81192 : CollatzResearch.WordTrace tailWord_81192 prefixEnd_81192 37058241155512506334765 := by
  unfold tailWord_81192
  simp only [CollatzResearch.WordTrace]
  refine ⟨1480657760931362667370915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1974210347908483556494553 1480657760931362667370915)
  ·
    refine ⟨2220986641397044001056373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1480657760931362667370915 2220986641397044001056373)
    ·
      refine ⟨208217497630972875099035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2220986641397044001056373 208217497630972875099035)
      ·
        refine ⟨312326246446459312648553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 208217497630972875099035 312326246446459312648553)
        ·
          refine ⟨234244684834844484486415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 312326246446459312648553 234244684834844484486415)
          ·
            refine ⟨351367027252266726729623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 234244684834844484486415 351367027252266726729623)
            ·
              refine ⟨527050540878400090094435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 351367027252266726729623 527050540878400090094435)
              ·
                refine ⟨790575811317600135141653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 527050540878400090094435 790575811317600135141653)
                ·
                  refine ⟨37058241155512506334765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 790575811317600135141653 37058241155512506334765)
                  ·
                    rfl

theorem cell20_81192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 1, 6].length) (baseStart_81192 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81192 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81192 prefixEnd_81192 := by exact prefixLift 81192
  have htrace : WordTrace (prefixWord ++ tailWord_81192) baseStart_81192 baseEnd_81192 := by
    simpa [prefixWord, tailWord_81192, baseEnd_81192] using wordTrace_append hprefix tailTrace_81192
  have hstable : (prefixWord ++ tailWord_81192).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81192).length < 2 ^ (prefixWord ++ tailWord_81192).sum := by decide
  have hdescent : baseEnd_81192 < baseStart_81192 := by decide
  rcases family_descends (prefixWord ++ tailWord_81192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81223 : List Nat := [1, 1, 4, 1, 2, 3, 3, 2, 3]
def baseStart_81223 : Nat := 118140960795 + 81223 * 2 ^ 59
def prefixEnd_81223 : Nat := 4983230072969 + 3 ^ 40 * 81223 * 2
def baseEnd_81223 : Nat := 37072390400214176301305

theorem tailTrace_81223 : CollatzResearch.WordTrace tailWord_81223 prefixEnd_81223 37072390400214176301305 := by
  unfold tailWord_81223
  simp only [CollatzResearch.WordTrace]
  refine ⟨2962446184750417629120323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1974964123166945086080215 2962446184750417629120323)
  ·
    refine ⟨4443669277125626443680485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2962446184750417629120323 4443669277125626443680485)
    ·
      refine ⟨833187989461054958190091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4443669277125626443680485 833187989461054958190091)
      ·
        refine ⟨1249781984191582437285137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833187989461054958190091 1249781984191582437285137)
        ·
          refine ⟨937336488143686827963853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1249781984191582437285137 937336488143686827963853)
          ·
            refine ⟨351501183053882560486445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 937336488143686827963853 351501183053882560486445)
            ·
              refine ⟨131812943645205960182417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 351501183053882560486445 131812943645205960182417)
              ·
                refine ⟨98859707733904470136813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 131812943645205960182417 98859707733904470136813)
                ·
                  refine ⟨37072390400214176301305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 98859707733904470136813 37072390400214176301305)
                  ·
                    rfl

theorem cell20_81223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 3, 2, 3].length) (baseStart_81223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81223 prefixEnd_81223 := by exact prefixLift 81223
  have htrace : WordTrace (prefixWord ++ tailWord_81223) baseStart_81223 baseEnd_81223 := by
    simpa [prefixWord, tailWord_81223, baseEnd_81223] using wordTrace_append hprefix tailTrace_81223
  have hstable : (prefixWord ++ tailWord_81223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81223).length < 2 ^ (prefixWord ++ tailWord_81223).sum := by decide
  have hdescent : baseEnd_81223 < baseStart_81223 := by decide
  rcases family_descends (prefixWord ++ tailWord_81223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81230 : List Nat := [4, 1, 1, 1, 1, 1, 6, 1, 4]
def baseStart_81230 : Nat := 118140960795 + 81230 * 2 ^ 59
def prefixEnd_81230 : Nat := 4983230072969 + 3 ^ 40 * 81230 * 2
def baseEnd_81230 : Nat := 37075585390953263067943

theorem tailTrace_81230 : CollatzResearch.WordTrace tailWord_81230 prefixEnd_81230 37075585390953263067943 := by
  unfold tailWord_81230
  simp only [CollatzResearch.WordTrace]
  refine ⟨370337686965632228078143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1975134330483371883083429 370337686965632228078143)
  ·
    refine ⟨555506530448448342117215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 370337686965632228078143 555506530448448342117215)
    ·
      refine ⟨833259795672672513175823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 555506530448448342117215 833259795672672513175823)
      ·
        refine ⟨1249889693509008769763735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 833259795672672513175823 1249889693509008769763735)
        ·
          refine ⟨1874834540263513154645603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1249889693509008769763735 1874834540263513154645603)
          ·
            refine ⟨2812251810395269731968405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1874834540263513154645603 2812251810395269731968405)
            ·
              refine ⟨131824303612278268686019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2812251810395269731968405 131824303612278268686019)
              ·
                refine ⟨197736455418417403029029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 131824303612278268686019 197736455418417403029029)
                ·
                  refine ⟨37075585390953263067943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 197736455418417403029029 37075585390953263067943)
                  ·
                    rfl

theorem cell20_81230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 6, 1, 4].length) (baseStart_81230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81230 prefixEnd_81230 := by exact prefixLift 81230
  have htrace : WordTrace (prefixWord ++ tailWord_81230) baseStart_81230 baseEnd_81230 := by
    simpa [prefixWord, tailWord_81230, baseEnd_81230] using wordTrace_append hprefix tailTrace_81230
  have hstable : (prefixWord ++ tailWord_81230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81230).length < 2 ^ (prefixWord ++ tailWord_81230).sum := by decide
  have hdescent : baseEnd_81230 < baseStart_81230 := by decide
  rcases family_descends (prefixWord ++ tailWord_81230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81281 : List Nat := [1, 2, 4, 3, 2, 1, 3, 2, 2]
def baseStart_81281 : Nat := 118140960795 + 81281 * 2 ^ 59
def prefixEnd_81281 : Nat := 4983230072969 + 3 ^ 40 * 81281 * 2
def baseEnd_81281 : Nat := 37098863180623752367735

theorem tailTrace_81281 : CollatzResearch.WordTrace tailWord_81281 prefixEnd_81281 37098863180623752367735 := by
  unfold tailWord_81281
  simp only [CollatzResearch.WordTrace]
  refine ⟨2964561618540293534731697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1976374412360195689821131 2964561618540293534731697)
  ·
    refine ⟨2223421213905220151048773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2964561618540293534731697 2223421213905220151048773)
    ·
      refine ⟨416891477607228778321645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2223421213905220151048773 416891477607228778321645)
      ·
        refine ⟨156334304102710791870617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 416891477607228778321645 156334304102710791870617)
        ·
          refine ⟨117250728077033093902963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156334304102710791870617 117250728077033093902963)
          ·
            refine ⟨175876092115549640854445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117250728077033093902963 175876092115549640854445)
            ·
              refine ⟨65953534543331115320417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 175876092115549640854445 65953534543331115320417)
              ·
                refine ⟨49465150907498336490313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65953534543331115320417 49465150907498336490313)
                ·
                  refine ⟨37098863180623752367735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49465150907498336490313 37098863180623752367735)
                  ·
                    rfl

theorem cell20_81281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 3, 2, 2].length) (baseStart_81281 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81281 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81281 prefixEnd_81281 := by exact prefixLift 81281
  have htrace : WordTrace (prefixWord ++ tailWord_81281) baseStart_81281 baseEnd_81281 := by
    simpa [prefixWord, tailWord_81281, baseEnd_81281] using wordTrace_append hprefix tailTrace_81281
  have hstable : (prefixWord ++ tailWord_81281).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81281).length < 2 ^ (prefixWord ++ tailWord_81281).sum := by decide
  have hdescent : baseEnd_81281 < baseStart_81281 := by decide
  rcases family_descends (prefixWord ++ tailWord_81281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81340 : List Nat := [2, 2, 2, 4, 2, 1, 1, 4, 2]
def baseStart_81340 : Nat := 118140960795 + 81340 * 2 ^ 59
def prefixEnd_81340 : Nat := 4983230072969 + 3 ^ 40 * 81340 * 2
def baseEnd_81340 : Nat := 37125792388281769400827

theorem tailTrace_81340 : CollatzResearch.WordTrace tailWord_81340 prefixEnd_81340 37125792388281769400827 := by
  unfold tailWord_81340
  simp only [CollatzResearch.WordTrace]
  refine ⟨1483356762663273305564737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1977809016884364407419649 1483356762663273305564737)
  ·
    refine ⟨1112517571997454979173553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1483356762663273305564737 1112517571997454979173553)
    ·
      refine ⟨834388178998091234380165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1112517571997454979173553 834388178998091234380165)
      ·
        refine ⟨156447783562142106446281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 834388178998091234380165 156447783562142106446281)
        ·
          refine ⟨117335837671606579834711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 156447783562142106446281 117335837671606579834711)
          ·
            refine ⟨176003756507409869752067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 117335837671606579834711 176003756507409869752067)
            ·
              refine ⟨264005634761114804628101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176003756507409869752067 264005634761114804628101)
              ·
                refine ⟨49501056517709025867769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 264005634761114804628101 49501056517709025867769)
                ·
                  refine ⟨37125792388281769400827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49501056517709025867769 37125792388281769400827)
                  ·
                    rfl

theorem cell20_81340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 4, 2].length) (baseStart_81340 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81340 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81340 prefixEnd_81340 := by exact prefixLift 81340
  have htrace : WordTrace (prefixWord ++ tailWord_81340) baseStart_81340 baseEnd_81340 := by
    simpa [prefixWord, tailWord_81340, baseEnd_81340] using wordTrace_append hprefix tailTrace_81340
  have hstable : (prefixWord ++ tailWord_81340).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81340).length < 2 ^ (prefixWord ++ tailWord_81340).sum := by decide
  have hdescent : baseEnd_81340 < baseStart_81340 := by decide
  rcases family_descends (prefixWord ++ tailWord_81340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81427 : List Nat := [1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_81427 : Nat := 118140960795 + 81427 * 2 ^ 59
def prefixEnd_81427 : Nat := 4983230072969 + 3 ^ 40 * 81427 * 2
def baseEnd_81427 : Nat := 12388500519632044500157

theorem tailTrace_81427 : CollatzResearch.WordTrace tailWord_81427 prefixEnd_81427 12388500519632044500157 := by
  unfold tailWord_81427
  simp only [CollatzResearch.WordTrace]
  refine ⟨2969886676011360469546535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1979924450674240313031023 2969886676011360469546535)
  ·
    refine ⟨4454830014017040704319803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2969886676011360469546535 4454830014017040704319803)
    ·
      refine ⟨6682245021025561056479705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4454830014017040704319803 6682245021025561056479705)
      ·
        refine ⟨5011683765769170792359779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6682245021025561056479705 5011683765769170792359779)
        ·
          refine ⟨7517525648653756188539669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5011683765769170792359779 7517525648653756188539669)
          ·
            refine ⟨352384014780644821337797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7517525648653756188539669 352384014780644821337797)
            ·
              refine ⟨66072002771370904000837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 352384014780644821337797 66072002771370904000837)
              ·
                refine ⟨12388500519632044500157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66072002771370904000837 12388500519632044500157)
                ·
                  rfl

theorem cell20_81427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_81427 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81427 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81427 prefixEnd_81427 := by exact prefixLift 81427
  have htrace : WordTrace (prefixWord ++ tailWord_81427) baseStart_81427 baseEnd_81427 := by
    simpa [prefixWord, tailWord_81427, baseEnd_81427] using wordTrace_append hprefix tailTrace_81427
  have hstable : (prefixWord ++ tailWord_81427).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81427).length < 2 ^ (prefixWord ++ tailWord_81427).sum := by decide
  have hdescent : baseEnd_81427 < baseStart_81427 := by decide
  rcases family_descends (prefixWord ++ tailWord_81427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81465 : List Nat := [1, 2, 1, 5, 1, 3, 2, 5]
def baseStart_81465 : Nat := 118140960795 + 81465 * 2 ^ 59
def prefixEnd_81465 : Nat := 4983230072969 + 3 ^ 40 * 81465 * 2
def baseEnd_81465 : Nat := 12394281931445630077883

theorem tailTrace_81465 : CollatzResearch.WordTrace tailWord_81465 prefixEnd_81465 12394281931445630077883 := by
  unfold tailWord_81465
  simp only [CollatzResearch.WordTrace]
  refine ⟨2971272649873692959429849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1980848433249128639619899 2971272649873692959429849)
  ·
    refine ⟨2228454487405269719572387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2971272649873692959429849 2228454487405269719572387)
    ·
      refine ⟨3342681731107904579358581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2228454487405269719572387 3342681731107904579358581)
      ·
        refine ⟨313376412291366054314867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3342681731107904579358581 313376412291366054314867)
        ·
          refine ⟨470064618437049081472301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313376412291366054314867 470064618437049081472301)
          ·
            refine ⟨176274231913893405552113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470064618437049081472301 176274231913893405552113)
            ·
              refine ⟨132205673935420054164085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176274231913893405552113 132205673935420054164085)
              ·
                refine ⟨12394281931445630077883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132205673935420054164085 12394281931445630077883)
                ·
                  rfl

theorem cell20_81465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 2, 5].length) (baseStart_81465 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81465 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81465 prefixEnd_81465 := by exact prefixLift 81465
  have htrace : WordTrace (prefixWord ++ tailWord_81465) baseStart_81465 baseEnd_81465 := by
    simpa [prefixWord, tailWord_81465, baseEnd_81465] using wordTrace_append hprefix tailTrace_81465
  have hstable : (prefixWord ++ tailWord_81465).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81465).length < 2 ^ (prefixWord ++ tailWord_81465).sum := by decide
  have hdescent : baseEnd_81465 < baseStart_81465 := by decide
  rcases family_descends (prefixWord ++ tailWord_81465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81496 : List Nat := [2, 1, 2, 2, 1, 2, 1, 7, 2]
def baseStart_81496 : Nat := 118140960795 + 81496 * 2 ^ 59
def prefixEnd_81496 : Nat := 4983230072969 + 3 ^ 40 * 81496 * 2
def baseEnd_81496 : Nat := 37196995039038560200189

theorem tailTrace_81496 : CollatzResearch.WordTrace tailWord_81496 prefixEnd_81496 37196995039038560200189 := by
  unfold tailWord_81496
  simp only [CollatzResearch.WordTrace]
  refine ⟨1486201656380692626904171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1981602208507590169205561 1486201656380692626904171)
  ·
    refine ⟨2229302484571038940356257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1486201656380692626904171 2229302484571038940356257)
    ·
      refine ⟨1671976863428279205267193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2229302484571038940356257 1671976863428279205267193)
      ·
        refine ⟨1253982647571209403950395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1671976863428279205267193 1253982647571209403950395)
        ·
          refine ⟨1880973971356814105925593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1253982647571209403950395 1880973971356814105925593)
          ·
            refine ⟨1410730478517610579444195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1880973971356814105925593 1410730478517610579444195)
            ·
              refine ⟨2116095717776415869166293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1410730478517610579444195 2116095717776415869166293)
              ·
                refine ⟨49595993385384746933585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2116095717776415869166293 49595993385384746933585)
                ·
                  refine ⟨37196995039038560200189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49595993385384746933585 37196995039038560200189)
                  ·
                    rfl

theorem cell20_81496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 1, 7, 2].length) (baseStart_81496 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81496 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81496 prefixEnd_81496 := by exact prefixLift 81496
  have htrace : WordTrace (prefixWord ++ tailWord_81496) baseStart_81496 baseEnd_81496 := by
    simpa [prefixWord, tailWord_81496, baseEnd_81496] using wordTrace_append hprefix tailTrace_81496
  have hstable : (prefixWord ++ tailWord_81496).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81496).length < 2 ^ (prefixWord ++ tailWord_81496).sum := by decide
  have hdescent : baseEnd_81496 < baseStart_81496 := by decide
  rcases family_descends (prefixWord ++ tailWord_81496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81513 : List Nat := [1, 2, 1, 1, 1, 4, 6, 2, 2]
def baseStart_81513 : Nat := 118140960795 + 81513 * 2 ^ 59
def prefixEnd_81513 : Nat := 4983230072969 + 3 ^ 40 * 81513 * 2
def baseEnd_81513 : Nat := 37204754302262056633453

theorem tailTrace_81513 : CollatzResearch.WordTrace tailWord_81513 prefixEnd_81513 37204754302262056633453 := by
  unfold tailWord_81513
  simp only [CollatzResearch.WordTrace]
  refine ⟨2973023353699797157177193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1982015569133198104784795 2973023353699797157177193)
  ·
    refine ⟨2229767515274847867882895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2973023353699797157177193 2229767515274847867882895)
    ·
      refine ⟨3344651272912271801824343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2229767515274847867882895 3344651272912271801824343)
      ·
        refine ⟨5016976909368407702736515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3344651272912271801824343 5016976909368407702736515)
        ·
          refine ⟨7525465364052611554104773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5016976909368407702736515 7525465364052611554104773)
          ·
            refine ⟨1411024755759864666394645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7525465364052611554104773 1411024755759864666394645)
            ·
              refine ⟨66141785426243656237249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1411024755759864666394645 66141785426243656237249)
              ·
                refine ⟨49606339069682742177937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66141785426243656237249 49606339069682742177937)
                ·
                  refine ⟨37204754302262056633453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49606339069682742177937 37204754302262056633453)
                  ·
                    rfl

theorem cell20_81513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 6, 2, 2].length) (baseStart_81513 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81513 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81513 prefixEnd_81513 := by exact prefixLift 81513
  have htrace : WordTrace (prefixWord ++ tailWord_81513) baseStart_81513 baseEnd_81513 := by
    simpa [prefixWord, tailWord_81513, baseEnd_81513] using wordTrace_append hprefix tailTrace_81513
  have hstable : (prefixWord ++ tailWord_81513).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81513).length < 2 ^ (prefixWord ++ tailWord_81513).sum := by decide
  have hdescent : baseEnd_81513 < baseStart_81513 := by decide
  rcases family_descends (prefixWord ++ tailWord_81513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81541 : List Nat := [1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_81541 : Nat := 118140960795 + 81541 * 2 ^ 59
def prefixEnd_81541 : Nat := 4983230072969 + 3 ^ 40 * 81541 * 2
def baseEnd_81541 : Nat := 12405844755072801233335

theorem tailTrace_81541 : CollatzResearch.WordTrace tailWord_81541 prefixEnd_81541 12405844755072801233335 := by
  unfold tailWord_81541
  simp only [CollatzResearch.WordTrace]
  refine ⟨2974044597598357939196477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1982696398398905292797651 2974044597598357939196477)
  ·
    refine ⟨1115266724099384227198679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2974044597598357939196477 1115266724099384227198679)
    ·
      refine ⟨1672900086149076340798019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1115266724099384227198679 1672900086149076340798019)
      ·
        refine ⟨2509350129223614511197029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1672900086149076340798019 2509350129223614511197029)
        ·
          refine ⟨470503149229427720849443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2509350129223614511197029 470503149229427720849443)
          ·
            refine ⟨705754723844141581274165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470503149229427720849443 705754723844141581274165)
            ·
              refine ⟨66164505360388273244453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 705754723844141581274165 66164505360388273244453)
              ·
                refine ⟨12405844755072801233335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66164505360388273244453 12405844755072801233335)
                ·
                  rfl

theorem cell20_81541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_81541 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81541 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81541 prefixEnd_81541 := by exact prefixLift 81541
  have htrace : WordTrace (prefixWord ++ tailWord_81541) baseStart_81541 baseEnd_81541 := by
    simpa [prefixWord, tailWord_81541, baseEnd_81541] using wordTrace_append hprefix tailTrace_81541
  have hstable : (prefixWord ++ tailWord_81541).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81541).length < 2 ^ (prefixWord ++ tailWord_81541).sum := by decide
  have hdescent : baseEnd_81541 < baseStart_81541 := by decide
  rcases family_descends (prefixWord ++ tailWord_81541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81572 : List Nat := [2, 3, 1, 2, 2, 3, 2, 1, 4]
def baseStart_81572 : Nat := 118140960795 + 81572 * 2 ^ 59
def prefixEnd_81572 : Nat := 4983230072969 + 3 ^ 40 * 81572 * 2
def baseEnd_81572 : Nat := 37231683509920073666545

theorem tailTrace_81572 : CollatzResearch.WordTrace tailWord_81572 prefixEnd_81572 37231683509920073666545 := by
  unfold tailWord_81572
  simp only [CollatzResearch.WordTrace]
  refine ⟨1487587630243025116787485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1983450173657366822383313 1487587630243025116787485)
  ·
    refine ⟨557845361341134418795307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1487587630243025116787485 557845361341134418795307)
    ·
      refine ⟨836768042011701628192961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557845361341134418795307 836768042011701628192961)
      ·
        refine ⟨627576031508776221144721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 836768042011701628192961 627576031508776221144721)
        ·
          refine ⟨470682023631582165858541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 627576031508776221144721 470682023631582165858541)
          ·
            refine ⟨176505758861843312196953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 470682023631582165858541 176505758861843312196953)
            ·
              refine ⟨132379319146382484147715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176505758861843312196953 132379319146382484147715)
              ·
                refine ⟨198568978719573726221573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132379319146382484147715 198568978719573726221573)
                ·
                  refine ⟨37231683509920073666545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198568978719573726221573 37231683509920073666545)
                  ·
                    rfl

theorem cell20_81572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 2, 1, 4].length) (baseStart_81572 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81572 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81572 prefixEnd_81572 := by exact prefixLift 81572
  have htrace : WordTrace (prefixWord ++ tailWord_81572) baseStart_81572 baseEnd_81572 := by
    simpa [prefixWord, tailWord_81572, baseEnd_81572] using wordTrace_append hprefix tailTrace_81572
  have hstable : (prefixWord ++ tailWord_81572).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81572).length < 2 ^ (prefixWord ++ tailWord_81572).sum := by decide
  have hdescent : baseEnd_81572 < baseStart_81572 := by decide
  rcases family_descends (prefixWord ++ tailWord_81572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81586 : List Nat := [3, 2, 1, 1, 1, 2, 2, 5, 3]
def baseStart_81586 : Nat := 118140960795 + 81586 * 2 ^ 59
def prefixEnd_81586 : Nat := 4983230072969 + 3 ^ 40 * 81586 * 2
def baseEnd_81586 : Nat := 37238073491398247199821

theorem tailTrace_81586 : CollatzResearch.WordTrace tailWord_81586 prefixEnd_81586 37238073491398247199821 := by
  unfold tailWord_81586
  simp only [CollatzResearch.WordTrace]
  refine ⟨743921470608832656146153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1983790588290220416389741 743921470608832656146153)
  ·
    refine ⟨557941102956624492109615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 743921470608832656146153 557941102956624492109615)
    ·
      refine ⟨836911654434936738164423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 557941102956624492109615 836911654434936738164423)
      ·
        refine ⟨1255367481652405107246635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 836911654434936738164423 1255367481652405107246635)
        ·
          refine ⟨1883051222478607660869953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255367481652405107246635 1883051222478607660869953)
          ·
            refine ⟨1412288416858955745652465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1883051222478607660869953 1412288416858955745652465)
            ·
              refine ⟨1059216312644216809239349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1412288416858955745652465 1059216312644216809239349)
              ·
                refine ⟨99301529310395325866189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1059216312644216809239349 99301529310395325866189)
                ·
                  refine ⟨37238073491398247199821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99301529310395325866189 37238073491398247199821)
                  ·
                    rfl

theorem cell20_81586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 5, 3].length) (baseStart_81586 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81586 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81586 prefixEnd_81586 := by exact prefixLift 81586
  have htrace : WordTrace (prefixWord ++ tailWord_81586) baseStart_81586 baseEnd_81586 := by
    simpa [prefixWord, tailWord_81586, baseEnd_81586] using wordTrace_append hprefix tailTrace_81586
  have hstable : (prefixWord ++ tailWord_81586).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81586).length < 2 ^ (prefixWord ++ tailWord_81586).sum := by decide
  have hdescent : baseEnd_81586 < baseStart_81586 := by decide
  rcases family_descends (prefixWord ++ tailWord_81586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81593 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 4]
def baseStart_81593 : Nat := 118140960795 + 81593 * 2 ^ 59
def prefixEnd_81593 : Nat := 4983230072969 + 3 ^ 40 * 81593 * 2
def baseEnd_81593 : Nat := 37241268482137333966459

theorem tailTrace_81593 : CollatzResearch.WordTrace tailWord_81593 prefixEnd_81593 37241268482137333966459 := by
  unfold tailWord_81593
  simp only [CollatzResearch.WordTrace]
  refine ⟨2975941193409970820089433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1983960795606647213392955 2975941193409970820089433)
  ·
    refine ⟨2231955895057478115067075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2975941193409970820089433 2231955895057478115067075)
    ·
      refine ⟨3347933842586217172600613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2231955895057478115067075 3347933842586217172600613)
      ·
        refine ⟨627737595484915719862615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3347933842586217172600613 627737595484915719862615)
        ·
          refine ⟨941606393227373579793923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 627737595484915719862615 941606393227373579793923)
          ·
            refine ⟨1412409589841060369690885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 941606393227373579793923 1412409589841060369690885)
            ·
              refine ⟨264826798095198819317041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1412409589841060369690885 264826798095198819317041)
              ·
                refine ⟨198620098571399114487781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 264826798095198819317041 198620098571399114487781)
                ·
                  refine ⟨37241268482137333966459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198620098571399114487781 37241268482137333966459)
                  ·
                    rfl

theorem cell20_81593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 4].length) (baseStart_81593 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81593 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81593 prefixEnd_81593 := by exact prefixLift 81593
  have htrace : WordTrace (prefixWord ++ tailWord_81593) baseStart_81593 baseEnd_81593 := by
    simpa [prefixWord, tailWord_81593, baseEnd_81593] using wordTrace_append hprefix tailTrace_81593
  have hstable : (prefixWord ++ tailWord_81593).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81593).length < 2 ^ (prefixWord ++ tailWord_81593).sum := by decide
  have hdescent : baseEnd_81593 < baseStart_81593 := by decide
  rcases family_descends (prefixWord ++ tailWord_81593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81596 : List Nat := [2, 2, 2, 3, 1, 4, 2, 4]
def baseStart_81596 : Nat := 118140960795 + 81596 * 2 ^ 59
def prefixEnd_81596 : Nat := 4983230072969 + 3 ^ 40 * 81596 * 2
def baseEnd_81596 : Nat := 12414212587960885622149

theorem tailTrace_81596 : CollatzResearch.WordTrace tailWord_81596 prefixEnd_81596 12414212587960885622149 := by
  unfold tailWord_81596
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488025306199551166224321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1984033741599401554965761 1488025306199551166224321)
  ·
    refine ⟨1116018979649663374668241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1488025306199551166224321 1116018979649663374668241)
    ·
      refine ⟨837014234737247531001181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1116018979649663374668241 837014234737247531001181)
      ·
        refine ⟨313880338026467824125443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 837014234737247531001181 313880338026467824125443)
        ·
          refine ⟨470820507039701736188165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 313880338026467824125443 470820507039701736188165)
          ·
            refine ⟨88278845069944075535281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 470820507039701736188165 88278845069944075535281)
            ·
              refine ⟨66209133802458056651461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88278845069944075535281 66209133802458056651461)
              ·
                refine ⟨12414212587960885622149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66209133802458056651461 12414212587960885622149)
                ·
                  rfl

theorem cell20_81596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 4, 2, 4].length) (baseStart_81596 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81596 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81596 prefixEnd_81596 := by exact prefixLift 81596
  have htrace : WordTrace (prefixWord ++ tailWord_81596) baseStart_81596 baseEnd_81596 := by
    simpa [prefixWord, tailWord_81596, baseEnd_81596] using wordTrace_append hprefix tailTrace_81596
  have hstable : (prefixWord ++ tailWord_81596).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81596).length < 2 ^ (prefixWord ++ tailWord_81596).sum := by decide
  have hdescent : baseEnd_81596 < baseStart_81596 := by decide
  rcases family_descends (prefixWord ++ tailWord_81596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81600 : List Nat := [2, 1, 1, 2, 4, 1, 3, 6]
def baseStart_81600 : Nat := 118140960795 + 81600 * 2 ^ 59
def prefixEnd_81600 : Nat := 4983230072969 + 3 ^ 40 * 81600 * 2
def baseEnd_81600 : Nat := 12414821157625473577699

theorem tailTrace_81600 : CollatzResearch.WordTrace tailWord_81600 prefixEnd_81600 12414821157625473577699 := by
  unfold tailWord_81600
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488098252192305507797127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1984131002923074010396169 1488098252192305507797127)
  ·
    refine ⟨2232147378288458261695691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1488098252192305507797127 2232147378288458261695691)
    ·
      refine ⟨3348221067432687392543537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2232147378288458261695691 3348221067432687392543537)
      ·
        refine ⟨2511165800574515544407653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3348221067432687392543537 2511165800574515544407653)
        ·
          refine ⟨470843587607721664576435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2511165800574515544407653 470843587607721664576435)
          ·
            refine ⟨706265381411582496864653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470843587607721664576435 706265381411582496864653)
            ·
              refine ⟨264849518029343436324245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 706265381411582496864653 264849518029343436324245)
              ·
                refine ⟨12414821157625473577699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 264849518029343436324245 12414821157625473577699)
                ·
                  rfl

theorem cell20_81600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 3, 6].length) (baseStart_81600 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81600 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81600 prefixEnd_81600 := by exact prefixLift 81600
  have htrace : WordTrace (prefixWord ++ tailWord_81600) baseStart_81600 baseEnd_81600 := by
    simpa [prefixWord, tailWord_81600, baseEnd_81600] using wordTrace_append hprefix tailTrace_81600
  have hstable : (prefixWord ++ tailWord_81600).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81600).length < 2 ^ (prefixWord ++ tailWord_81600).sum := by decide
  have hdescent : baseEnd_81600 < baseStart_81600 := by decide
  rcases family_descends (prefixWord ++ tailWord_81600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81607 : List Nat := [1, 1, 4, 1, 1, 1, 3, 1, 7]
def baseStart_81607 : Nat := 118140960795 + 81607 * 2 ^ 59
def prefixEnd_81607 : Nat := 4983230072969 + 3 ^ 40 * 81607 * 2
def baseEnd_81607 : Nat := 37247658463615507499735

theorem tailTrace_81607 : CollatzResearch.WordTrace tailWord_81607 prefixEnd_81607 37247658463615507499735 := by
  unfold tailWord_81607
  simp only [CollatzResearch.WordTrace]
  refine ⟨2976451815359251211099075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1984301210239500807399383 2976451815359251211099075)
  ·
    refine ⟨4464677723038876816648613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2976451815359251211099075 4464677723038876816648613)
    ·
      refine ⟨837127073069789403121615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4464677723038876816648613 837127073069789403121615)
      ·
        refine ⟨1255690609604684104682423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 837127073069789403121615 1255690609604684104682423)
        ·
          refine ⟨1883535914407026157023635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1255690609604684104682423 1883535914407026157023635)
          ·
            refine ⟨2825303871610539235535453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1883535914407026157023635 2825303871610539235535453)
            ·
              refine ⟨1059488951853952213325795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2825303871610539235535453 1059488951853952213325795)
              ·
                refine ⟨1589233427780928319988693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1059488951853952213325795 1589233427780928319988693)
                ·
                  refine ⟨37247658463615507499735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1589233427780928319988693 37247658463615507499735)
                  ·
                    rfl

theorem cell20_81607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 1, 7].length) (baseStart_81607 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81607 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81607 prefixEnd_81607 := by exact prefixLift 81607
  have htrace : WordTrace (prefixWord ++ tailWord_81607) baseStart_81607 baseEnd_81607 := by
    simpa [prefixWord, tailWord_81607, baseEnd_81607] using wordTrace_append hprefix tailTrace_81607
  have hstable : (prefixWord ++ tailWord_81607).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81607).length < 2 ^ (prefixWord ++ tailWord_81607).sum := by decide
  have hdescent : baseEnd_81607 < baseStart_81607 := by decide
  rcases family_descends (prefixWord ++ tailWord_81607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81624 : List Nat := [2, 1, 2, 2, 3, 1, 2, 4, 3]
def baseStart_81624 : Nat := 118140960795 + 81624 * 2 ^ 59
def prefixEnd_81624 : Nat := 4983230072969 + 3 ^ 40 * 81624 * 2
def baseEnd_81624 : Nat := 37255417726839003932999

theorem tailTrace_81624 : CollatzResearch.WordTrace tailWord_81624 prefixEnd_81624 37255417726839003932999 := by
  unfold tailWord_81624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1488535928148831557233963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1984714570865108742978617 1488535928148831557233963)
  ·
    refine ⟨2232803892223247335850945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1488535928148831557233963 2232803892223247335850945)
    ·
      refine ⟨1674602919167435501888209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2232803892223247335850945 1674602919167435501888209)
      ·
        refine ⟨1255952189375576626416157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1674602919167435501888209 1255952189375576626416157)
        ·
          refine ⟨470982071015841234906059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1255952189375576626416157 470982071015841234906059)
          ·
            refine ⟨706473106523761852359089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 470982071015841234906059 706473106523761852359089)
            ·
              refine ⟨529854829892821389269317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 706473106523761852359089 529854829892821389269317)
              ·
                refine ⟨99347780604904010487997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 529854829892821389269317 99347780604904010487997)
                ·
                  refine ⟨37255417726839003932999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99347780604904010487997 37255417726839003932999)
                  ·
                    rfl

theorem cell20_81624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 2, 4, 3].length) (baseStart_81624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81624 prefixEnd_81624 := by exact prefixLift 81624
  have htrace : WordTrace (prefixWord ++ tailWord_81624) baseStart_81624 baseEnd_81624 := by
    simpa [prefixWord, tailWord_81624, baseEnd_81624] using wordTrace_append hprefix tailTrace_81624
  have hstable : (prefixWord ++ tailWord_81624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81624).length < 2 ^ (prefixWord ++ tailWord_81624).sum := by decide
  have hdescent : baseEnd_81624 < baseStart_81624 := by decide
  rcases family_descends (prefixWord ++ tailWord_81624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81682 : List Nat := [3, 2, 4, 1, 1, 2, 1, 4, 2]
def baseStart_81682 : Nat := 118140960795 + 81682 * 2 ^ 59
def prefixEnd_81682 : Nat := 4983230072969 + 3 ^ 40 * 81682 * 2
def baseEnd_81682 : Nat := 37281890507248579999429

theorem tailTrace_81682 : CollatzResearch.WordTrace tailWord_81682 prefixEnd_81682 37281890507248579999429 := by
  unfold tailWord_81682
  simp only [CollatzResearch.WordTrace]
  refine ⟨744796822521884755019825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1986124860058359346719533 744796822521884755019825)
  ·
    refine ⟨558597616891413566264869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 744796822521884755019825 558597616891413566264869)
    ·
      refine ⟨104737053167140043674663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 558597616891413566264869 104737053167140043674663)
      ·
        refine ⟨157105579750710065511995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 104737053167140043674663 157105579750710065511995)
        ·
          refine ⟨235658369626065098267993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157105579750710065511995 235658369626065098267993)
          ·
            refine ⟨176743777219548823700995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235658369626065098267993 176743777219548823700995)
            ·
              refine ⟨265115665829323235551493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176743777219548823700995 265115665829323235551493)
              ·
                refine ⟨49709187342998106665905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 265115665829323235551493 49709187342998106665905)
                ·
                  refine ⟨37281890507248579999429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49709187342998106665905 37281890507248579999429)
                  ·
                    rfl

theorem cell20_81682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 2, 1, 4, 2].length) (baseStart_81682 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81682 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81682 prefixEnd_81682 := by exact prefixLift 81682
  have htrace : WordTrace (prefixWord ++ tailWord_81682) baseStart_81682 baseEnd_81682 := by
    simpa [prefixWord, tailWord_81682, baseEnd_81682] using wordTrace_append hprefix tailTrace_81682
  have hstable : (prefixWord ++ tailWord_81682).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81682).length < 2 ^ (prefixWord ++ tailWord_81682).sum := by decide
  have hdescent : baseEnd_81682 < baseStart_81682 := by decide
  rcases family_descends (prefixWord ++ tailWord_81682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81724 : List Nat := [2, 2, 2, 2, 1, 1, 3, 5, 2]
def baseStart_81724 : Nat := 118140960795 + 81724 * 2 ^ 59
def prefixEnd_81724 : Nat := 4983230072969 + 3 ^ 40 * 81724 * 2
def baseEnd_81724 : Nat := 37301060451683100599257

theorem tailTrace_81724 : CollatzResearch.WordTrace tailWord_81724 prefixEnd_81724 37301060451683100599257 := by
  unfold tailWord_81724
  simp only [CollatzResearch.WordTrace]
  refine ⟨1490359577967690096554113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1987146103956920128738817 1490359577967690096554113)
  ·
    refine ⟨1117769683475767572415585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1490359577967690096554113 1117769683475767572415585)
    ·
      refine ⟨838327262606825679311689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1117769683475767572415585 838327262606825679311689)
      ·
        refine ⟨628745446955119259483767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 838327262606825679311689 628745446955119259483767)
        ·
          refine ⟨943118170432678889225651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 628745446955119259483767 943118170432678889225651)
          ·
            refine ⟨1414677255649018333838477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 943118170432678889225651 1414677255649018333838477)
            ·
              refine ⟨530503970868381875189429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1414677255649018333838477 530503970868381875189429)
              ·
                refine ⟨49734747268910800799009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 530503970868381875189429 49734747268910800799009)
                ·
                  refine ⟨37301060451683100599257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49734747268910800799009 37301060451683100599257)
                  ·
                    rfl

theorem cell20_81724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 3, 5, 2].length) (baseStart_81724 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81724 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81724 prefixEnd_81724 := by exact prefixLift 81724
  have htrace : WordTrace (prefixWord ++ tailWord_81724) baseStart_81724 baseEnd_81724 := by
    simpa [prefixWord, tailWord_81724, baseEnd_81724] using wordTrace_append hprefix tailTrace_81724
  have hstable : (prefixWord ++ tailWord_81724).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81724).length < 2 ^ (prefixWord ++ tailWord_81724).sum := by decide
  have hdescent : baseEnd_81724 < baseStart_81724 := by decide
  rcases family_descends (prefixWord ++ tailWord_81724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81734 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 5]
def baseStart_81734 : Nat := 118140960795 + 81734 * 2 ^ 59
def prefixEnd_81734 : Nat := 4983230072969 + 3 ^ 40 * 81734 * 2
def baseEnd_81734 : Nat := 37305624724167510265883

theorem tailTrace_81734 : CollatzResearch.WordTrace tailWord_81734 prefixEnd_81734 37305624724167510265883 := by
  unfold tailWord_81734
  simp only [CollatzResearch.WordTrace]
  refine ⟨93158871434348496905383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1987389257266101267314837 93158871434348496905383)
  ·
    refine ⟨139738307151522745358075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93158871434348496905383 139738307151522745358075)
    ·
      refine ⟨209607460727284118037113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139738307151522745358075 209607460727284118037113)
      ·
        refine ⟨157205595545463088527835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209607460727284118037113 157205595545463088527835)
        ·
          refine ⟨235808393318194632791753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157205595545463088527835 235808393318194632791753)
          ·
            refine ⟨176856294988645974593815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235808393318194632791753 176856294988645974593815)
            ·
              refine ⟨265284442482968961890723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 176856294988645974593815 265284442482968961890723)
              ·
                refine ⟨397926663724453442836085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 265284442482968961890723 397926663724453442836085)
                ·
                  refine ⟨37305624724167510265883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 397926663724453442836085 37305624724167510265883)
                  ·
                    rfl

theorem cell20_81734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_81734 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81734 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81734 prefixEnd_81734 := by exact prefixLift 81734
  have htrace : WordTrace (prefixWord ++ tailWord_81734) baseStart_81734 baseEnd_81734 := by
    simpa [prefixWord, tailWord_81734, baseEnd_81734] using wordTrace_append hprefix tailTrace_81734
  have hstable : (prefixWord ++ tailWord_81734).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81734).length < 2 ^ (prefixWord ++ tailWord_81734).sum := by decide
  have hdescent : baseEnd_81734 < baseStart_81734 := by decide
  rcases family_descends (prefixWord ++ tailWord_81734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81741 : List Nat := [1, 6, 1, 2, 1, 2, 2, 1, 4]
def baseStart_81741 : Nat := 118140960795 + 81741 * 2 ^ 59
def prefixEnd_81741 : Nat := 4983230072969 + 3 ^ 40 * 81741 * 2
def baseEnd_81741 : Nat := 37308819714906597032521

theorem tailTrace_81741 : CollatzResearch.WordTrace tailWord_81741 prefixEnd_81741 37308819714906597032521 := by
  unfold tailWord_81741
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981339196873792096477077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1987559464582528064318051 2981339196873792096477077)
  ·
    refine ⟨139750274853459004522363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 2981339196873792096477077 139750274853459004522363)
    ·
      refine ⟨209625412280188506783545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 139750274853459004522363 209625412280188506783545)
      ·
        refine ⟨157219059210141380087659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209625412280188506783545 157219059210141380087659)
        ·
          refine ⟨235828588815212070131489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157219059210141380087659 235828588815212070131489)
          ·
            refine ⟨176871441611409052598617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 235828588815212070131489 176871441611409052598617)
            ·
              refine ⟨132653581208556789448963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 176871441611409052598617 132653581208556789448963)
              ·
                refine ⟨198980371812835184173445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 132653581208556789448963 198980371812835184173445)
                ·
                  refine ⟨37308819714906597032521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198980371812835184173445 37308819714906597032521)
                  ·
                    rfl

theorem cell20_81741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_81741 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81741 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81741 prefixEnd_81741 := by exact prefixLift 81741
  have htrace : WordTrace (prefixWord ++ tailWord_81741) baseStart_81741 baseEnd_81741 := by
    simpa [prefixWord, tailWord_81741, baseEnd_81741] using wordTrace_append hprefix tailTrace_81741
  have hstable : (prefixWord ++ tailWord_81741).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81741).length < 2 ^ (prefixWord ++ tailWord_81741).sum := by decide
  have hdescent : baseEnd_81741 < baseStart_81741 := by decide
  rcases family_descends (prefixWord ++ tailWord_81741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81745 : List Nat := [1, 2, 2, 1, 5, 1, 1, 3, 4]
def baseStart_81745 : Nat := 118140960795 + 81745 * 2 ^ 59
def prefixEnd_81745 : Nat := 4983230072969 + 3 ^ 40 * 81745 * 2
def baseEnd_81745 : Nat := 37310645423900360899171

theorem tailTrace_81745 : CollatzResearch.WordTrace tailWord_81745 prefixEnd_81745 37310645423900360899171 := by
  unfold tailWord_81745
  simp only [CollatzResearch.WordTrace]
  refine ⟨2981485088859300779622689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1987656725906200519748459 2981485088859300779622689)
  ·
    refine ⟨2236113816644475584717017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2981485088859300779622689 2236113816644475584717017)
    ·
      refine ⟨1677085362483356688537763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2236113816644475584717017 1677085362483356688537763)
      ·
        refine ⟨2515628043725035032806645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1677085362483356688537763 2515628043725035032806645)
        ·
          refine ⟨235840129099222034325623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 2515628043725035032806645 235840129099222034325623)
          ·
            refine ⟨353760193648833051488435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235840129099222034325623 353760193648833051488435)
            ·
              refine ⟨530640290473249577232653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 353760193648833051488435 530640290473249577232653)
              ·
                refine ⟨198990108927468591462245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 530640290473249577232653 198990108927468591462245)
                ·
                  refine ⟨37310645423900360899171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 198990108927468591462245 37310645423900360899171)
                  ·
                    rfl

theorem cell20_81745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 3, 4].length) (baseStart_81745 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81745 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81745 prefixEnd_81745 := by exact prefixLift 81745
  have htrace : WordTrace (prefixWord ++ tailWord_81745) baseStart_81745 baseEnd_81745 := by
    simpa [prefixWord, tailWord_81745, baseEnd_81745] using wordTrace_append hprefix tailTrace_81745
  have hstable : (prefixWord ++ tailWord_81745).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81745).length < 2 ^ (prefixWord ++ tailWord_81745).sum := by decide
  have hdescent : baseEnd_81745 < baseStart_81745 := by decide
  rcases family_descends (prefixWord ++ tailWord_81745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81762 : List Nat := [3, 3, 2, 1, 2, 1, 2, 2, 4]
def baseStart_81762 : Nat := 118140960795 + 81762 * 2 ^ 59
def prefixEnd_81762 : Nat := 4983230072969 + 3 ^ 40 * 81762 * 2
def baseEnd_81762 : Nat := 37318404687123857332435

theorem tailTrace_81762 : CollatzResearch.WordTrace tailWord_81762 prefixEnd_81762 37318404687123857332435 := by
  unfold tailWord_81762
  simp only [CollatzResearch.WordTrace]
  refine ⟨745526282449428170747885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1988070086531808455327693 745526282449428170747885)
  ·
    refine ⟨279572355918535564030457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 745526282449428170747885 279572355918535564030457)
    ·
      refine ⟨209679266938901673022843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 279572355918535564030457 209679266938901673022843)
      ·
        refine ⟨314518900408352509534265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 209679266938901673022843 314518900408352509534265)
        ·
          refine ⟨235889175306264382150699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 314518900408352509534265 235889175306264382150699)
          ·
            refine ⟨353833762959396573226049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 235889175306264382150699 353833762959396573226049)
            ·
              refine ⟨265375322219547429919537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 353833762959396573226049 265375322219547429919537)
              ·
                refine ⟨199031491664660572439653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 265375322219547429919537 199031491664660572439653)
                ·
                  refine ⟨37318404687123857332435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199031491664660572439653 37318404687123857332435)
                  ·
                    rfl

theorem cell20_81762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 2, 2, 4].length) (baseStart_81762 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81762 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81762 prefixEnd_81762 := by exact prefixLift 81762
  have htrace : WordTrace (prefixWord ++ tailWord_81762) baseStart_81762 baseEnd_81762 := by
    simpa [prefixWord, tailWord_81762, baseEnd_81762] using wordTrace_append hprefix tailTrace_81762
  have hstable : (prefixWord ++ tailWord_81762).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81762).length < 2 ^ (prefixWord ++ tailWord_81762).sum := by decide
  have hdescent : baseEnd_81762 < baseStart_81762 := by decide
  rcases family_descends (prefixWord ++ tailWord_81762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81797 : List Nat := [1, 3, 1, 1, 3, 2, 1, 3, 5]
def baseStart_81797 : Nat := 118140960795 + 81797 * 2 ^ 59
def prefixEnd_81797 : Nat := 4983230072969 + 3 ^ 40 * 81797 * 2
def baseEnd_81797 : Nat := 37334379640819291165625

theorem tailTrace_81797 : CollatzResearch.WordTrace tailWord_81797 prefixEnd_81797 37334379640819291165625 := by
  unfold tailWord_81797
  simp only [CollatzResearch.WordTrace]
  refine ⟨2983381684670913660515645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1988921123113942440343763 2983381684670913660515645)
  ·
    refine ⟨1118768131751592622693367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2983381684670913660515645 1118768131751592622693367)
    ·
      refine ⟨1678152197627388934040051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1118768131751592622693367 1678152197627388934040051)
      ·
        refine ⟨2517228296441083401060077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1678152197627388934040051 2517228296441083401060077)
        ·
          refine ⟨943960611165406275397529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2517228296441083401060077 943960611165406275397529)
          ·
            refine ⟨707970458374054706548147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 943960611165406275397529 707970458374054706548147)
            ·
              refine ⟨1061955687561082059822221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 707970458374054706548147 1061955687561082059822221)
              ·
                refine ⟨398233382835405772433333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1061955687561082059822221 398233382835405772433333)
                ·
                  refine ⟨37334379640819291165625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 398233382835405772433333 37334379640819291165625)
                  ·
                    rfl

theorem cell20_81797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 3, 5].length) (baseStart_81797 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81797 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81797 prefixEnd_81797 := by exact prefixLift 81797
  have htrace : WordTrace (prefixWord ++ tailWord_81797) baseStart_81797 baseEnd_81797 := by
    simpa [prefixWord, tailWord_81797, baseEnd_81797] using wordTrace_append hprefix tailTrace_81797
  have hstable : (prefixWord ++ tailWord_81797).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81797).length < 2 ^ (prefixWord ++ tailWord_81797).sum := by decide
  have hdescent : baseEnd_81797 < baseStart_81797 := by decide
  rcases family_descends (prefixWord ++ tailWord_81797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81806 : List Nat := [4, 1, 1, 5, 2, 1, 2, 1, 3]
def baseStart_81806 : Nat := 118140960795 + 81806 * 2 ^ 59
def prefixEnd_81806 : Nat := 4983230072969 + 3 ^ 40 * 81806 * 2
def baseEnd_81806 : Nat := 37338487486055259865589

theorem tailTrace_81806 : CollatzResearch.WordTrace tailWord_81806 prefixEnd_81806 37338487486055259865589 := by
  unfold tailWord_81806
  simp only [CollatzResearch.WordTrace]
  refine ⟨372963742704788524699159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1989139961092205465062181 372963742704788524699159)
  ·
    refine ⟨559445614057182787048739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 372963742704788524699159 559445614057182787048739)
    ·
      refine ⟨839168421085774180573109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559445614057182787048739 839168421085774180573109)
      ·
        refine ⟨78672039476791329428729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 839168421085774180573109 78672039476791329428729)
        ·
          refine ⟨59004029607593497071547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 78672039476791329428729 59004029607593497071547)
          ·
            refine ⟨88506044411390245607321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59004029607593497071547 88506044411390245607321)
            ·
              refine ⟨66379533308542684205491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 88506044411390245607321 66379533308542684205491)
              ·
                refine ⟨99569299962814026308237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66379533308542684205491 99569299962814026308237)
                ·
                  refine ⟨37338487486055259865589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99569299962814026308237 37338487486055259865589)
                  ·
                    rfl

theorem cell20_81806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 2, 1, 2, 1, 3].length) (baseStart_81806 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81806 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81806 prefixEnd_81806 := by exact prefixLift 81806
  have htrace : WordTrace (prefixWord ++ tailWord_81806) baseStart_81806 baseEnd_81806 := by
    simpa [prefixWord, tailWord_81806, baseEnd_81806] using wordTrace_append hprefix tailTrace_81806
  have hstable : (prefixWord ++ tailWord_81806).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81806).length < 2 ^ (prefixWord ++ tailWord_81806).sum := by decide
  have hdescent : baseEnd_81806 < baseStart_81806 := by decide
  rcases family_descends (prefixWord ++ tailWord_81806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81810 : List Nat := [3, 2, 3, 2, 1, 1, 4, 1, 3]
def baseStart_81810 : Nat := 118140960795 + 81810 * 2 ^ 59
def prefixEnd_81810 : Nat := 4983230072969 + 3 ^ 40 * 81810 * 2
def baseEnd_81810 : Nat := 37340313195049023732239

theorem tailTrace_81810 : CollatzResearch.WordTrace tailWord_81810 prefixEnd_81810 37340313195049023732239 := by
  unfold tailWord_81810
  simp only [CollatzResearch.WordTrace]
  refine ⟨745963958405954220184721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1989237222415877920492589 745963958405954220184721)
  ·
    refine ⟨559472968804465665138541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 745963958405954220184721 559472968804465665138541)
    ·
      refine ⟨209802363301674624426953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 559472968804465665138541 209802363301674624426953)
      ·
        refine ⟨157351772476255968320215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 209802363301674624426953 157351772476255968320215)
        ·
          refine ⟨236027658714383952480323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 157351772476255968320215 236027658714383952480323)
          ·
            refine ⟨354041488071575928720485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 236027658714383952480323 354041488071575928720485)
            ·
              refine ⟨66382779013420486635091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 354041488071575928720485 66382779013420486635091)
              ·
                refine ⟨99574168520130729952637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66382779013420486635091 99574168520130729952637)
                ·
                  refine ⟨37340313195049023732239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99574168520130729952637 37340313195049023732239)
                  ·
                    rfl

theorem cell20_81810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 4, 1, 3].length) (baseStart_81810 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81810 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81810 prefixEnd_81810 := by exact prefixLift 81810
  have htrace : WordTrace (prefixWord ++ tailWord_81810) baseStart_81810 baseEnd_81810 := by
    simpa [prefixWord, tailWord_81810, baseEnd_81810] using wordTrace_append hprefix tailTrace_81810
  have hstable : (prefixWord ++ tailWord_81810).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81810).length < 2 ^ (prefixWord ++ tailWord_81810).sum := by decide
  have hdescent : baseEnd_81810 < baseStart_81810 := by decide
  rcases family_descends (prefixWord ++ tailWord_81810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81828 : List Nat := [2, 3, 1, 2, 1, 3, 2, 6]
def baseStart_81828 : Nat := 118140960795 + 81828 * 2 ^ 59
def prefixEnd_81828 : Nat := 4983230072969 + 3 ^ 40 * 81828 * 2
def baseEnd_81828 : Nat := 12449509628506987044055

theorem tailTrace_81828 : CollatzResearch.WordTrace tailWord_81828 prefixEnd_81828 12449509628506987044055 := by
  unfold tailWord_81828
  simp only [CollatzResearch.WordTrace]
  refine ⟨1492256173779302977447069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1989674898372403969929425 1492256173779302977447069)
  ·
    refine ⟨559596065167238616542651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1492256173779302977447069 559596065167238616542651)
    ·
      refine ⟨839394097750857924813977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 559596065167238616542651 839394097750857924813977)
      ·
        refine ⟨629545573313143443610483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 839394097750857924813977 629545573313143443610483)
        ·
          refine ⟨944318359969715165415725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 629545573313143443610483 944318359969715165415725)
          ·
            refine ⟨354119384988643187030897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 944318359969715165415725 354119384988643187030897)
            ·
              refine ⟨265589538741482390273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354119384988643187030897 265589538741482390273173)
              ·
                refine ⟨12449509628506987044055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 265589538741482390273173 12449509628506987044055)
                ·
                  rfl

theorem cell20_81828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 2, 6].length) (baseStart_81828 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81828 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81828 prefixEnd_81828 := by exact prefixLift 81828
  have htrace : WordTrace (prefixWord ++ tailWord_81828) baseStart_81828 baseEnd_81828 := by
    simpa [prefixWord, tailWord_81828, baseEnd_81828] using wordTrace_append hprefix tailTrace_81828
  have hstable : (prefixWord ++ tailWord_81828).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81828).length < 2 ^ (prefixWord ++ tailWord_81828).sum := by decide
  have hdescent : baseEnd_81828 < baseStart_81828 := by decide
  rcases family_descends (prefixWord ++ tailWord_81828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81866 : List Nat := [3, 1, 2, 1, 2, 1, 5, 5]
def baseStart_81866 : Nat := 118140960795 + 81866 * 2 ^ 59
def prefixEnd_81866 : Nat := 4983230072969 + 3 ^ 40 * 81866 * 2
def baseEnd_81866 : Nat := 12455291040320572621781

theorem tailTrace_81866 : CollatzResearch.WordTrace tailWord_81866 prefixEnd_81866 12455291040320572621781 := by
  unfold tailWord_81866
  simp only [CollatzResearch.WordTrace]
  refine ⟨746474580355234611194363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1990598880947292296518301 746474580355234611194363)
  ·
    refine ⟨1119711870532851916791545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 746474580355234611194363 1119711870532851916791545)
    ·
      refine ⟨839783902899638937593659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1119711870532851916791545 839783902899638937593659)
      ·
        refine ⟨1259675854349458406390489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 839783902899638937593659 1259675854349458406390489)
        ·
          refine ⟨944756890762093804792867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1259675854349458406390489 944756890762093804792867)
          ·
            refine ⟨1417135336143140707189301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 944756890762093804792867 1417135336143140707189301)
            ·
              refine ⟨132856437763419441298997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1417135336143140707189301 132856437763419441298997)
              ·
                refine ⟨12455291040320572621781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 132856437763419441298997 12455291040320572621781)
                ·
                  rfl

theorem cell20_81866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 5, 5].length) (baseStart_81866 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81866 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81866 prefixEnd_81866 := by exact prefixLift 81866
  have htrace : WordTrace (prefixWord ++ tailWord_81866) baseStart_81866 baseEnd_81866 := by
    simpa [prefixWord, tailWord_81866, baseEnd_81866] using wordTrace_append hprefix tailTrace_81866
  have hstable : (prefixWord ++ tailWord_81866).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81866).length < 2 ^ (prefixWord ++ tailWord_81866).sum := by decide
  have hdescent : baseEnd_81866 < baseStart_81866 := by decide
  rcases family_descends (prefixWord ++ tailWord_81866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81966 : List Nat := [4, 1, 3, 1, 1, 2, 2, 1, 5]
def baseStart_81966 : Nat := 118140960795 + 81966 * 2 ^ 59
def prefixEnd_81966 : Nat := 4983230072969 + 3 ^ 40 * 81966 * 2
def baseEnd_81966 : Nat := 37411515845805814531601

theorem tailTrace_81966 : CollatzResearch.WordTrace tailWord_81966 prefixEnd_81966 37411515845805814531601 := by
  unfold tailWord_81966
  simp only [CollatzResearch.WordTrace]
  refine ⟨373693202632331940427219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1993030414039103682278501 373693202632331940427219)
  ·
    refine ⟨560539803948497910640829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 373693202632331940427219 560539803948497910640829)
    ·
      refine ⟨210202426480686716490311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 560539803948497910640829 210202426480686716490311)
      ·
        refine ⟨315303639721030074735467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210202426480686716490311 315303639721030074735467)
        ·
          refine ⟨472955459581545112103201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315303639721030074735467 472955459581545112103201)
          ·
            refine ⟨354716594686158834077401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 472955459581545112103201 354716594686158834077401)
            ·
              refine ⟨266037446014619125558051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 354716594686158834077401 266037446014619125558051)
              ·
                refine ⟨399056169021928688337077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 266037446014619125558051 399056169021928688337077)
                ·
                  refine ⟨37411515845805814531601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 399056169021928688337077 37411515845805814531601)
                  ·
                    rfl

theorem cell20_81966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 2, 2, 1, 5].length) (baseStart_81966 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81966 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81966 prefixEnd_81966 := by exact prefixLift 81966
  have htrace : WordTrace (prefixWord ++ tailWord_81966) baseStart_81966 baseEnd_81966 := by
    simpa [prefixWord, tailWord_81966, baseEnd_81966] using wordTrace_append hprefix tailTrace_81966
  have hstable : (prefixWord ++ tailWord_81966).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81966).length < 2 ^ (prefixWord ++ tailWord_81966).sum := by decide
  have hdescent : baseEnd_81966 < baseStart_81966 := by decide
  rcases family_descends (prefixWord ++ tailWord_81966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81969 : List Nat := [1, 2, 2, 3, 1, 4, 3, 2, 2]
def baseStart_81969 : Nat := 118140960795 + 81969 * 2 ^ 59
def prefixEnd_81969 : Nat := 4983230072969 + 3 ^ 40 * 81969 * 2
def baseEnd_81969 : Nat := 37412885127551137431589

theorem tailTrace_81969 : CollatzResearch.WordTrace tailWord_81969 prefixEnd_81969 37412885127551137431589 := by
  unfold tailWord_81969
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989655040047787035776961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1993103360031858023851307 2989655040047787035776961)
  ·
    refine ⟨2242241280035840276832721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2989655040047787035776961 2242241280035840276832721)
    ·
      refine ⟨1681680960026880207624541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2242241280035840276832721 1681680960026880207624541)
      ·
        refine ⟨630630360010080077859203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1681680960026880207624541 630630360010080077859203)
        ·
          refine ⟨945945540015120116788805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630630360010080077859203 945945540015120116788805)
          ·
            refine ⟨177364788752835021897901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 945945540015120116788805 177364788752835021897901)
            ·
              refine ⟨66511795782313133211713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177364788752835021897901 66511795782313133211713)
              ·
                refine ⟨49883846836734849908785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 66511795782313133211713 49883846836734849908785)
                ·
                  refine ⟨37412885127551137431589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49883846836734849908785 37412885127551137431589)
                  ·
                    rfl

theorem cell20_81969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_81969 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81969 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81969 prefixEnd_81969 := by exact prefixLift 81969
  have htrace : WordTrace (prefixWord ++ tailWord_81969) baseStart_81969 baseEnd_81969 := by
    simpa [prefixWord, tailWord_81969, baseEnd_81969] using wordTrace_append hprefix tailTrace_81969
  have hstable : (prefixWord ++ tailWord_81969).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81969).length < 2 ^ (prefixWord ++ tailWord_81969).sum := by decide
  have hdescent : baseEnd_81969 < baseStart_81969 := by decide
  rcases family_descends (prefixWord ++ tailWord_81969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81973 : List Nat := [1, 3, 3, 1, 1, 1, 5, 1, 4]
def baseStart_81973 : Nat := 118140960795 + 81973 * 2 ^ 59
def prefixEnd_81973 : Nat := 4983230072969 + 3 ^ 40 * 81973 * 2
def baseEnd_81973 : Nat := 37414710836544901298239

theorem tailTrace_81973 : CollatzResearch.WordTrace tailWord_81973 prefixEnd_81973 37414710836544901298239 := by
  unfold tailWord_81973
  simp only [CollatzResearch.WordTrace]
  refine ⟨2989800932033295718922573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1993200621355530479281715 2989800932033295718922573)
  ·
    refine ⟨1121175349512485894595965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2989800932033295718922573 1121175349512485894595965)
    ·
      refine ⟨420440756067182210473487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1121175349512485894595965 420440756067182210473487)
      ·
        refine ⟨630661134100773315710231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 420440756067182210473487 630661134100773315710231)
        ·
          refine ⟨945991701151159973565347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 630661134100773315710231 945991701151159973565347)
          ·
            refine ⟨1418987551726739960348021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 945991701151159973565347 1418987551726739960348021)
            ·
              refine ⟨133030082974381871282627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1418987551726739960348021 133030082974381871282627)
              ·
                refine ⟨199545124461572806923941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133030082974381871282627 199545124461572806923941)
                ·
                  refine ⟨37414710836544901298239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 199545124461572806923941 37414710836544901298239)
                  ·
                    rfl

theorem cell20_81973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 5, 1, 4].length) (baseStart_81973 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81973 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81973 prefixEnd_81973 := by exact prefixLift 81973
  have htrace : WordTrace (prefixWord ++ tailWord_81973) baseStart_81973 baseEnd_81973 := by
    simpa [prefixWord, tailWord_81973, baseEnd_81973] using wordTrace_append hprefix tailTrace_81973
  have hstable : (prefixWord ++ tailWord_81973).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81973).length < 2 ^ (prefixWord ++ tailWord_81973).sum := by decide
  have hdescent : baseEnd_81973 < baseStart_81973 := by decide
  rcases family_descends (prefixWord ++ tailWord_81973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81980 : List Nat := [2, 2, 2, 2, 2, 1, 4, 5]
def baseStart_81980 : Nat := 118140960795 + 81980 * 2 ^ 59
def prefixEnd_81980 : Nat := 4983230072969 + 3 ^ 40 * 81980 * 2
def baseEnd_81980 : Nat := 12472635275761329354959

theorem tailTrace_81980 : CollatzResearch.WordTrace tailWord_81980 prefixEnd_81980 12472635275761329354959 := by
  unfold tailWord_81980
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495028121503967957213697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1993370828671957276284929 1495028121503967957213697)
  ·
    refine ⟨1121271091127975967910273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495028121503967957213697 1121271091127975967910273)
    ·
      refine ⟨840953318345981975932705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1121271091127975967910273 840953318345981975932705)
      ·
        refine ⟨630714988759486481949529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 840953318345981975932705 630714988759486481949529)
        ·
          refine ⟨473036241569614861462147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 630714988759486481949529 473036241569614861462147)
          ·
            refine ⟨709554362354422292193221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473036241569614861462147 709554362354422292193221)
            ·
              refine ⟨133041442941454179786229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 709554362354422292193221 133041442941454179786229)
              ·
                refine ⟨12472635275761329354959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133041442941454179786229 12472635275761329354959)
                ·
                  rfl

theorem cell20_81980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_81980 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81980 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81980 prefixEnd_81980 := by exact prefixLift 81980
  have htrace : WordTrace (prefixWord ++ tailWord_81980) baseStart_81980 baseEnd_81980 := by
    simpa [prefixWord, tailWord_81980, baseEnd_81980] using wordTrace_append hprefix tailTrace_81980
  have hstable : (prefixWord ++ tailWord_81980).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81980).length < 2 ^ (prefixWord ++ tailWord_81980).sum := by decide
  have hdescent : baseEnd_81980 < baseStart_81980 := by decide
  rcases family_descends (prefixWord ++ tailWord_81980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81990 : List Nat := [6, 1, 1, 1, 1, 1, 2, 1, 6]
def baseStart_81990 : Nat := 118140960795 + 81990 * 2 ^ 59
def prefixEnd_81990 : Nat := 4983230072969 + 3 ^ 40 * 81990 * 2
def baseEnd_81990 : Nat := 37422470099768397731503

theorem tailTrace_81990 : CollatzResearch.WordTrace tailWord_81990 prefixEnd_81990 37422470099768397731503 := by
  unfold tailWord_81990
  simp only [CollatzResearch.WordTrace]
  refine ⟨93450655405365863196607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 1993613981981138414860949 93450655405365863196607)
  ·
    refine ⟨140175983108048794794911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 93450655405365863196607 140175983108048794794911)
    ·
      refine ⟨210263974662073192192367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 140175983108048794794911 210263974662073192192367)
      ·
        refine ⟨315395961993109788288551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 210263974662073192192367 315395961993109788288551)
        ·
          refine ⟨473093942989664682432827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 315395961993109788288551 473093942989664682432827)
          ·
            refine ⟨709640914484497023649241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 473093942989664682432827 709640914484497023649241)
            ·
              refine ⟨532230685863372767736931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 709640914484497023649241 532230685863372767736931)
              ·
                refine ⟨798346028795059151605397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 532230685863372767736931 798346028795059151605397)
                ·
                  refine ⟨37422470099768397731503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 798346028795059151605397 37422470099768397731503)
                  ·
                    rfl

theorem cell20_81990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_81990 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81990 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81990 prefixEnd_81990 := by exact prefixLift 81990
  have htrace : WordTrace (prefixWord ++ tailWord_81990) baseStart_81990 baseEnd_81990 := by
    simpa [prefixWord, tailWord_81990, baseEnd_81990] using wordTrace_append hprefix tailTrace_81990
  have hstable : (prefixWord ++ tailWord_81990).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81990).length < 2 ^ (prefixWord ++ tailWord_81990).sum := by decide
  have hdescent : baseEnd_81990 < baseStart_81990 := by decide
  rcases family_descends (prefixWord ++ tailWord_81990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_81994 : List Nat := [3, 1, 2, 1, 1, 2, 1, 3, 6]
def baseStart_81994 : Nat := 118140960795 + 81994 * 2 ^ 59
def prefixEnd_81994 : Nat := 4983230072969 + 3 ^ 40 * 81994 * 2
def baseEnd_81994 : Nat := 37424295808762161598153

theorem tailTrace_81994 : CollatzResearch.WordTrace tailWord_81994 prefixEnd_81994 37424295808762161598153 := by
  unfold tailWord_81994
  simp only [CollatzResearch.WordTrace]
  refine ⟨747641716239304076359259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1993711243304810870291357 747641716239304076359259)
  ·
    refine ⟨1121462574358956114538889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 747641716239304076359259 1121462574358956114538889)
    ·
      refine ⟨841096930769217085904167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1121462574358956114538889 841096930769217085904167)
      ·
        refine ⟨1261645396153825628856251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 841096930769217085904167 1261645396153825628856251)
        ·
          refine ⟨1892468094230738443284377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1261645396153825628856251 1892468094230738443284377)
          ·
            refine ⟨1419351070673053832463283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1892468094230738443284377 1419351070673053832463283)
            ·
              refine ⟨2129026606009580748694925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1419351070673053832463283 2129026606009580748694925)
              ·
                refine ⟨798384977253592780760597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2129026606009580748694925 798384977253592780760597)
                ·
                  refine ⟨37424295808762161598153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 798384977253592780760597 37424295808762161598153)
                  ·
                    rfl

theorem cell20_81994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_81994 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_81994 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_81994 prefixEnd_81994 := by exact prefixLift 81994
  have htrace : WordTrace (prefixWord ++ tailWord_81994) baseStart_81994 baseEnd_81994 := by
    simpa [prefixWord, tailWord_81994, baseEnd_81994] using wordTrace_append hprefix tailTrace_81994
  have hstable : (prefixWord ++ tailWord_81994).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_81994).length < 2 ^ (prefixWord ++ tailWord_81994).sum := by decide
  have hdescent : baseEnd_81994 < baseStart_81994 := by decide
  rcases family_descends (prefixWord ++ tailWord_81994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82014 : List Nat := [4, 4, 1, 1, 2, 8]
def baseStart_82014 : Nat := 118140960795 + 82014 * 2 ^ 59
def prefixEnd_82014 : Nat := 4983230072969 + 3 ^ 40 * 82014 * 2
def baseEnd_82014 : Nat := 1386423124212258553015

theorem tailTrace_82014 : CollatzResearch.WordTrace tailWord_82014 prefixEnd_82014 1386423124212258553015 := by
  unfold tailWord_82014
  simp only [CollatzResearch.WordTrace]
  refine ⟨373912040610594965145637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 1994197549923173147443397 373912040610594965145637)
  ·
    refine ⟨70108507614486555964807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 373912040610594965145637 70108507614486555964807)
    ·
      refine ⟨105162761421729833947211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 70108507614486555964807 105162761421729833947211)
      ·
        refine ⟨157744142132594750920817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 105162761421729833947211 157744142132594750920817)
        ·
          refine ⟨118308106599446063190613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 157744142132594750920817 118308106599446063190613)
          ·
            refine ⟨1386423124212258553015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 118308106599446063190613 1386423124212258553015)
            ·
              rfl

theorem cell20_82014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 8].length) (baseStart_82014 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82014 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82014 prefixEnd_82014 := by exact prefixLift 82014
  have htrace : WordTrace (prefixWord ++ tailWord_82014) baseStart_82014 baseEnd_82014 := by
    simpa [prefixWord, tailWord_82014, baseEnd_82014] using wordTrace_append hprefix tailTrace_82014
  have hstable : (prefixWord ++ tailWord_82014).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82014).length < 2 ^ (prefixWord ++ tailWord_82014).sum := by decide
  have hdescent : baseEnd_82014 < baseStart_82014 := by decide
  rcases family_descends (prefixWord ++ tailWord_82014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82018 : List Nat := [3, 3, 2, 2, 10]
def baseStart_82018 : Nat := 118140960795 + 82018 * 2 ^ 59
def prefixEnd_82018 : Nat := 4983230072969 + 3 ^ 40 * 82018 * 2
def baseEnd_82018 : Nat := 462163581021293145655

theorem tailTrace_82018 : CollatzResearch.WordTrace tailWord_82018 prefixEnd_82018 462163581021293145655 := by
  unfold tailWord_82018
  simp only [CollatzResearch.WordTrace]
  refine ⟨747860554217567101077677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1994294811246845602873805 747860554217567101077677)
  ·
    refine ⟨280447707831587662904129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 747860554217567101077677 280447707831587662904129)
    ·
      refine ⟨210335780873690747178097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 280447707831587662904129 210335780873690747178097)
      ·
        refine ⟨157751835655268060383573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210335780873690747178097 157751835655268060383573)
        ·
          refine ⟨462163581021293145655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 10 157751835655268060383573 462163581021293145655)
          ·
            rfl

theorem cell20_82018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 10].length) (baseStart_82018 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82018 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82018 prefixEnd_82018 := by exact prefixLift 82018
  have htrace : WordTrace (prefixWord ++ tailWord_82018) baseStart_82018 baseEnd_82018 := by
    simpa [prefixWord, tailWord_82018, baseEnd_82018] using wordTrace_append hprefix tailTrace_82018
  have hstable : (prefixWord ++ tailWord_82018).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82018).length < 2 ^ (prefixWord ++ tailWord_82018).sum := by decide
  have hdescent : baseEnd_82018 < baseStart_82018 := by decide
  rcases family_descends (prefixWord ++ tailWord_82018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82028 : List Nat := [2, 2, 1, 1, 3, 4, 1, 4, 2]
def baseStart_82028 : Nat := 118140960795 + 82028 * 2 ^ 59
def prefixEnd_82028 : Nat := 4983230072969 + 3 ^ 40 * 82028 * 2
def baseEnd_82028 : Nat := 37439814335209154464681

theorem tailTrace_82028 : CollatzResearch.WordTrace tailWord_82028 prefixEnd_82028 37439814335209154464681 := by
  unfold tailWord_82028
  simp only [CollatzResearch.WordTrace]
  refine ⟨1495903473417020056087369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1994537964556026741449825 1495903473417020056087369)
  ·
    refine ⟨1121927605062765042065527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1495903473417020056087369 1121927605062765042065527)
    ·
      refine ⟨1682891407594147563098291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1121927605062765042065527 1682891407594147563098291)
      ·
        refine ⟨2524337111391221344647437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1682891407594147563098291 2524337111391221344647437)
        ·
          refine ⟨946626416771708004242789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2524337111391221344647437 946626416771708004242789)
          ·
            refine ⟨177492453144695250795523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 946626416771708004242789 177492453144695250795523)
            ·
              refine ⟨266238679717042876193285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177492453144695250795523 266238679717042876193285)
              ·
                refine ⟨49919752446945539286241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 266238679717042876193285 49919752446945539286241)
                ·
                  refine ⟨37439814335209154464681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 49919752446945539286241 37439814335209154464681)
                  ·
                    rfl

theorem cell20_82028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 4, 1, 4, 2].length) (baseStart_82028 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82028 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82028 prefixEnd_82028 := by exact prefixLift 82028
  have htrace : WordTrace (prefixWord ++ tailWord_82028) baseStart_82028 baseEnd_82028 := by
    simpa [prefixWord, tailWord_82028, baseEnd_82028] using wordTrace_append hprefix tailTrace_82028
  have hstable : (prefixWord ++ tailWord_82028).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82028).length < 2 ^ (prefixWord ++ tailWord_82028).sum := by decide
  have hdescent : baseEnd_82028 < baseStart_82028 := by decide
  rcases family_descends (prefixWord ++ tailWord_82028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82080 : List Nat := [2, 1, 1, 4, 2, 2, 3, 2, 3]
def baseStart_82080 : Nat := 118140960795 + 82080 * 2 ^ 59
def prefixEnd_82080 : Nat := 4983230072969 + 3 ^ 40 * 82080 * 2
def baseEnd_82080 : Nat := 37463548552128084731135

theorem tailTrace_82080 : CollatzResearch.WordTrace tailWord_82080 prefixEnd_82080 37463548552128084731135 := by
  unfold tailWord_82080
  simp only [CollatzResearch.WordTrace]
  refine ⟨1496851771322826496533847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1995802361763768662045129 1496851771322826496533847)
  ·
    refine ⟨2245277656984239744800771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1496851771322826496533847 2245277656984239744800771)
    ·
      refine ⟨3367916485476359617201157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2245277656984239744800771 3367916485476359617201157)
      ·
        refine ⟨631484341026817428225217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3367916485476359617201157 631484341026817428225217)
        ·
          refine ⟨473613255770113071168913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 631484341026817428225217 473613255770113071168913)
          ·
            refine ⟨355209941827584803376685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 473613255770113071168913 355209941827584803376685)
            ·
              refine ⟨133203728185344301266257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355209941827584803376685 133203728185344301266257)
              ·
                refine ⟨99902796139008225949693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133203728185344301266257 99902796139008225949693)
                ·
                  refine ⟨37463548552128084731135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 99902796139008225949693 37463548552128084731135)
                  ·
                    rfl

theorem cell20_82080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 2, 3, 2, 3].length) (baseStart_82080 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82080 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82080 prefixEnd_82080 := by exact prefixLift 82080
  have htrace : WordTrace (prefixWord ++ tailWord_82080) baseStart_82080 baseEnd_82080 := by
    simpa [prefixWord, tailWord_82080, baseEnd_82080] using wordTrace_append hprefix tailTrace_82080
  have hstable : (prefixWord ++ tailWord_82080).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82080).length < 2 ^ (prefixWord ++ tailWord_82080).sum := by decide
  have hdescent : baseEnd_82080 < baseStart_82080 := by decide
  rcases family_descends (prefixWord ++ tailWord_82080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82208 : List Nat := [2, 1, 1, 5, 2, 1, 3, 5]
def baseStart_82208 : Nat := 118140960795 + 82208 * 2 ^ 59
def prefixEnd_82208 : Nat := 4983230072969 + 3 ^ 40 * 82208 * 2
def baseEnd_82208 : Nat := 12507323746642842821315

theorem tailTrace_82208 : CollatzResearch.WordTrace tailWord_82208 prefixEnd_82208 12507323746642842821315 := by
  unfold tailWord_82208
  simp only [CollatzResearch.WordTrace]
  refine ⟨1499186043090965426863639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 1998914724121287235818185 1499186043090965426863639)
  ·
    refine ⟨2248779064636448140295459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1499186043090965426863639 2248779064636448140295459)
    ·
      refine ⟨3373168596954672210443189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2248779064636448140295459 3373168596954672210443189)
      ·
        refine ⟨316234555964500519729049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3373168596954672210443189 316234555964500519729049)
        ·
          refine ⟨237175916973375389796787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 316234555964500519729049 237175916973375389796787)
          ·
            refine ⟨355763875460063084695181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 237175916973375389796787 355763875460063084695181)
            ·
              refine ⟨133411453297523656760693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 355763875460063084695181 133411453297523656760693)
              ·
                refine ⟨12507323746642842821315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133411453297523656760693 12507323746642842821315)
                ·
                  rfl

theorem cell20_82208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 3, 5].length) (baseStart_82208 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82208 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82208 prefixEnd_82208 := by exact prefixLift 82208
  have htrace : WordTrace (prefixWord ++ tailWord_82208) baseStart_82208 baseEnd_82208 := by
    simpa [prefixWord, tailWord_82208, baseEnd_82208] using wordTrace_append hprefix tailTrace_82208
  have hstable : (prefixWord ++ tailWord_82208).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82208).length < 2 ^ (prefixWord ++ tailWord_82208).sum := by decide
  have hdescent : baseEnd_82208 < baseStart_82208 := by decide
  rcases family_descends (prefixWord ++ tailWord_82208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82218 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 4]
def baseStart_82218 : Nat := 118140960795 + 82218 * 2 ^ 59
def prefixEnd_82218 : Nat := 4983230072969 + 3 ^ 40 * 82218 * 2
def baseEnd_82218 : Nat := 37526535512412938130571

theorem tailTrace_82218 : CollatzResearch.WordTrace tailWord_82218 prefixEnd_82218 37526535512412938130571 := by
  unfold tailWord_82218
  simp only [CollatzResearch.WordTrace]
  refine ⟨749684204036425640397827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 1999157877430468374394205 749684204036425640397827)
  ·
    refine ⟨1124526306054638460596741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 749684204036425640397827 1124526306054638460596741)
    ·
      refine ⟨210848682385244711361889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1124526306054638460596741 210848682385244711361889)
      ·
        refine ⟨158136511788933533521417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 210848682385244711361889 158136511788933533521417)
        ·
          refine ⟨118602383841700150141063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 158136511788933533521417 118602383841700150141063)
          ·
            refine ⟨177903575762550225211595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118602383841700150141063 177903575762550225211595)
            ·
              refine ⟨266855363643825337817393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 177903575762550225211595 266855363643825337817393)
              ·
                refine ⟨200141522732869003363045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 266855363643825337817393 200141522732869003363045)
                ·
                  refine ⟨37526535512412938130571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200141522732869003363045 37526535512412938130571)
                  ·
                    rfl

theorem cell20_82218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 4].length) (baseStart_82218 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82218 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82218 prefixEnd_82218 := by exact prefixLift 82218
  have htrace : WordTrace (prefixWord ++ tailWord_82218) baseStart_82218 baseEnd_82218 := by
    simpa [prefixWord, tailWord_82218, baseEnd_82218] using wordTrace_append hprefix tailTrace_82218
  have hstable : (prefixWord ++ tailWord_82218).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82218).length < 2 ^ (prefixWord ++ tailWord_82218).sum := by decide
  have hdescent : baseEnd_82218 < baseStart_82218 := by decide
  rcases family_descends (prefixWord ++ tailWord_82218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82225 : List Nat := [1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_82225 : Nat := 118140960795 + 82225 * 2 ^ 59
def prefixEnd_82225 : Nat := 4983230072969 + 3 ^ 40 * 82225 * 2
def baseEnd_82225 : Nat := 12509910167717341632403

theorem tailTrace_82225 : CollatzResearch.WordTrace tailWord_82225 prefixEnd_82225 12509910167717341632403 := by
  unfold tailWord_82225
  simp only [CollatzResearch.WordTrace]
  refine ⟨2998992127120342757096129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 1999328084746895171397419 2998992127120342757096129)
  ·
    refine ⟨2249244095340257067822097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2998992127120342757096129 2249244095340257067822097)
    ·
      refine ⟨1686933071505192800866573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2249244095340257067822097 1686933071505192800866573)
      ·
        refine ⟨632599901814447300324965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1686933071505192800866573 632599901814447300324965)
        ·
          refine ⟨118612481590208868810931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 632599901814447300324965 118612481590208868810931)
          ·
            refine ⟨177918722385313303216397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118612481590208868810931 177918722385313303216397)
            ·
              refine ⟨66719520894492488706149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 177918722385313303216397 66719520894492488706149)
              ·
                refine ⟨12509910167717341632403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 66719520894492488706149 12509910167717341632403)
                ·
                  rfl

theorem cell20_82225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_82225 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82225 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82225 prefixEnd_82225 := by exact prefixLift 82225
  have htrace : WordTrace (prefixWord ++ tailWord_82225) baseStart_82225 baseEnd_82225 := by
    simpa [prefixWord, tailWord_82225, baseEnd_82225] using wordTrace_append hprefix tailTrace_82225
  have hstable : (prefixWord ++ tailWord_82225).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82225).length < 2 ^ (prefixWord ++ tailWord_82225).sum := by decide
  have hdescent : baseEnd_82225 < baseStart_82225 := by decide
  rcases family_descends (prefixWord ++ tailWord_82225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82284 : List Nat := [2, 2, 1, 1, 6, 1, 1, 6]
def baseStart_82284 : Nat := 118140960795 + 82284 * 2 ^ 59
def prefixEnd_82284 : Nat := 4983230072969 + 3 ^ 40 * 82284 * 2
def baseEnd_82284 : Nat := 12518886570270013976767

theorem tailTrace_82284 : CollatzResearch.WordTrace tailWord_82284 prefixEnd_82284 12518886570270013976767 := by
  unfold tailWord_82284
  simp only [CollatzResearch.WordTrace]
  refine ⟨1500572016953297916746953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2000762689271063888995937 1500572016953297916746953)
  ·
    refine ⟨1125429012714973437560215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1500572016953297916746953 1125429012714973437560215)
    ·
      refine ⟨1688143519072460156340323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1125429012714973437560215 1688143519072460156340323)
      ·
        refine ⟨2532215278608690234510485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1688143519072460156340323 2532215278608690234510485)
        ·
          refine ⟨118697591184782354742679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 2532215278608690234510485 118697591184782354742679)
          ·
            refine ⟨178046386777173532114019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118697591184782354742679 178046386777173532114019)
            ·
              refine ⟨267069580165760298171029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178046386777173532114019 267069580165760298171029)
              ·
                refine ⟨12518886570270013976767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 267069580165760298171029 12518886570270013976767)
                ·
                  rfl

theorem cell20_82284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 1, 6].length) (baseStart_82284 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82284 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82284 prefixEnd_82284 := by exact prefixLift 82284
  have htrace : WordTrace (prefixWord ++ tailWord_82284) baseStart_82284 baseEnd_82284 := by
    simpa [prefixWord, tailWord_82284, baseEnd_82284] using wordTrace_append hprefix tailTrace_82284
  have hstable : (prefixWord ++ tailWord_82284).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82284).length < 2 ^ (prefixWord ++ tailWord_82284).sum := by decide
  have hdescent : baseEnd_82284 < baseStart_82284 := by decide
  rcases family_descends (prefixWord ++ tailWord_82284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82315 : List Nat := [1, 1, 1, 1, 4, 6, 1, 1, 4]
def baseStart_82315 : Nat := 118140960795 + 82315 * 2 ^ 59
def prefixEnd_82315 : Nat := 4983230072969 + 3 ^ 40 * 82315 * 2
def baseEnd_82315 : Nat := 37570808955511711896841

theorem tailTrace_82315 : CollatzResearch.WordTrace tailWord_82315 prefixEnd_82315 37570808955511711896841 := by
  unfold tailWord_82315
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002274696794288127872399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2001516464529525418581599 3002274696794288127872399)
  ·
    refine ⟨4503412045191432191808599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3002274696794288127872399 4503412045191432191808599)
    ·
      refine ⟨6755118067787148287712899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4503412045191432191808599 6755118067787148287712899)
      ·
        refine ⟨10132677101680722431569349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6755118067787148287712899 10132677101680722431569349)
        ·
          refine ⟨1899876956565135455919253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10132677101680722431569349 1899876956565135455919253)
          ·
            refine ⟨89056732338990724496215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1899876956565135455919253 89056732338990724496215)
            ·
              refine ⟨133585098508486086744323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89056732338990724496215 133585098508486086744323)
              ·
                refine ⟨200377647762729130116485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 133585098508486086744323 200377647762729130116485)
                ·
                  refine ⟨37570808955511711896841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 200377647762729130116485 37570808955511711896841)
                  ·
                    rfl

theorem cell20_82315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 1, 1, 4].length) (baseStart_82315 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82315 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82315 prefixEnd_82315 := by exact prefixLift 82315
  have htrace : WordTrace (prefixWord ++ tailWord_82315) baseStart_82315 baseEnd_82315 := by
    simpa [prefixWord, tailWord_82315, baseEnd_82315] using wordTrace_append hprefix tailTrace_82315
  have hstable : (prefixWord ++ tailWord_82315).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82315).length < 2 ^ (prefixWord ++ tailWord_82315).sum := by decide
  have hdescent : baseEnd_82315 < baseStart_82315 := by decide
  rcases family_descends (prefixWord ++ tailWord_82315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82329 : List Nat := [1, 2, 1, 2, 1, 4, 3, 3, 3]
def baseStart_82329 : Nat := 118140960795 + 82329 * 2 ^ 59
def prefixEnd_82329 : Nat := 4983230072969 + 3 ^ 40 * 82329 * 2
def baseEnd_82329 : Nat := 37577198936989885430117

theorem tailTrace_82329 : CollatzResearch.WordTrace tailWord_82329 prefixEnd_82329 37577198936989885430117 := by
  unfold tailWord_82329
  simp only [CollatzResearch.WordTrace]
  refine ⟨3002785318743568518882041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2001856879162379012588027 3002785318743568518882041)
  ·
    refine ⟨2252088989057676389161531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3002785318743568518882041 2252088989057676389161531)
    ·
      refine ⟨3378133483586514583742297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2252088989057676389161531 3378133483586514583742297)
      ·
        refine ⟨2533600112689885937806723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3378133483586514583742297 2533600112689885937806723)
        ·
          refine ⟨3800400169034828906710085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2533600112689885937806723 3800400169034828906710085)
          ·
            refine ⟨712575031694030420008141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3800400169034828906710085 712575031694030420008141)
            ·
              refine ⟨267215636885261407503053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 712575031694030420008141 267215636885261407503053)
              ·
                refine ⟨100205863831973027813645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 267215636885261407503053 100205863831973027813645)
                ·
                  refine ⟨37577198936989885430117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100205863831973027813645 37577198936989885430117)
                  ·
                    rfl

theorem cell20_82329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_82329 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82329 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82329 prefixEnd_82329 := by exact prefixLift 82329
  have htrace : WordTrace (prefixWord ++ tailWord_82329) baseStart_82329 baseEnd_82329 := by
    simpa [prefixWord, tailWord_82329, baseEnd_82329] using wordTrace_append hprefix tailTrace_82329
  have hstable : (prefixWord ++ tailWord_82329).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82329).length < 2 ^ (prefixWord ++ tailWord_82329).sum := by decide
  have hdescent : baseEnd_82329 < baseStart_82329 := by decide
  rcases family_descends (prefixWord ++ tailWord_82329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82356 : List Nat := [2, 5, 2, 2, 2, 7]
def baseStart_82356 : Nat := 118140960795 + 82356 * 2 ^ 59
def prefixEnd_82356 : Nat := 4983230072969 + 3 ^ 40 * 82356 * 2
def baseEnd_82356 : Nat := 1392204536025844130741

theorem tailTrace_82356 : CollatzResearch.WordTrace tailWord_82356 prefixEnd_82356 1392204536025844130741 := by
  unfold tailWord_82356
  simp only [CollatzResearch.WordTrace]
  refine ⟨1501885044822876065057461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2002513393097168086743281 1501885044822876065057461)
  ·
    refine ⟨140801722952144631099137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 1501885044822876065057461 140801722952144631099137)
    ·
      refine ⟨105601292214108473324353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 140801722952144631099137 105601292214108473324353)
      ·
        refine ⟨79200969160581354993265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 105601292214108473324353 79200969160581354993265)
        ·
          refine ⟨59400726870436016244949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 79200969160581354993265 59400726870436016244949)
          ·
            refine ⟨1392204536025844130741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 59400726870436016244949 1392204536025844130741)
            ·
              rfl

theorem cell20_82356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 7].length) (baseStart_82356 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82356 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82356 prefixEnd_82356 := by exact prefixLift 82356
  have htrace : WordTrace (prefixWord ++ tailWord_82356) baseStart_82356 baseEnd_82356 := by
    simpa [prefixWord, tailWord_82356, baseEnd_82356] using wordTrace_append hprefix tailTrace_82356
  have hstable : (prefixWord ++ tailWord_82356).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82356).length < 2 ^ (prefixWord ++ tailWord_82356).sum := by decide
  have hdescent : baseEnd_82356 < baseStart_82356 := by decide
  rcases family_descends (prefixWord ++ tailWord_82356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82408 : List Nat := [2, 1, 4, 1, 1, 4, 2, 3, 2]
def baseStart_82408 : Nat := 118140960795 + 82408 * 2 ^ 59
def prefixEnd_82408 : Nat := 4983230072969 + 3 ^ 40 * 82408 * 2
def baseEnd_82408 : Nat := 37613256689616721796461

theorem tailTrace_82408 : CollatzResearch.WordTrace tailWord_82408 prefixEnd_82408 37613256689616721796461 := by
  unfold tailWord_82408
  simp only [CollatzResearch.WordTrace]
  refine ⟨1502833342728682505503939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2003777790304910007338585 1502833342728682505503939)
  ·
    refine ⟨2254250014093023758255909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1502833342728682505503939 2254250014093023758255909)
    ·
      refine ⟨422671877642441954672983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2254250014093023758255909 422671877642441954672983)
      ·
        refine ⟨634007816463662932009475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 422671877642441954672983 634007816463662932009475)
        ·
          refine ⟨951011724695494398014213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 634007816463662932009475 951011724695494398014213)
          ·
            refine ⟨178314698380405199627665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 951011724695494398014213 178314698380405199627665)
            ·
              refine ⟨133736023785303899720749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178314698380405199627665 133736023785303899720749)
              ·
                refine ⟨50151008919488962395281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 133736023785303899720749 50151008919488962395281)
                ·
                  refine ⟨37613256689616721796461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50151008919488962395281 37613256689616721796461)
                  ·
                    rfl

theorem cell20_82408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 2, 3, 2].length) (baseStart_82408 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82408 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82408 prefixEnd_82408 := by exact prefixLift 82408
  have htrace : WordTrace (prefixWord ++ tailWord_82408) baseStart_82408 baseEnd_82408 := by
    simpa [prefixWord, tailWord_82408, baseEnd_82408] using wordTrace_append hprefix tailTrace_82408
  have hstable : (prefixWord ++ tailWord_82408).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82408).length < 2 ^ (prefixWord ++ tailWord_82408).sum := by decide
  have hdescent : baseEnd_82408 < baseStart_82408 := by decide
  rcases family_descends (prefixWord ++ tailWord_82408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82418 : List Nat := [3, 2, 1, 4, 3, 1, 1, 2, 3]
def baseStart_82418 : Nat := 118140960795 + 82418 * 2 ^ 59
def prefixEnd_82418 : Nat := 4983230072969 + 3 ^ 40 * 82418 * 2
def baseEnd_82418 : Nat := 37617820962101131463087

theorem tailTrace_82418 : CollatzResearch.WordTrace tailWord_82418 prefixEnd_82418 37617820962101131463087 := by
  unfold tailWord_82418
  simp only [CollatzResearch.WordTrace]
  refine ⟨751507853855284179717977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2004020943614091145914605 751507853855284179717977)
  ·
    refine ⟨563630890391463134788483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 751507853855284179717977 563630890391463134788483)
    ·
      refine ⟨845446335587194702182725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563630890391463134788483 845446335587194702182725)
      ·
        refine ⟨158521187922599006659261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 845446335587194702182725 158521187922599006659261)
        ·
          refine ⟨59445445470974627497223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 158521187922599006659261 59445445470974627497223)
          ·
            refine ⟨89168168206461941245835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 59445445470974627497223 89168168206461941245835)
            ·
              refine ⟨133752252309692911868753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89168168206461941245835 133752252309692911868753)
              ·
                refine ⟨100314189232269683901565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 133752252309692911868753 100314189232269683901565)
                ·
                  refine ⟨37617820962101131463087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100314189232269683901565 37617820962101131463087)
                  ·
                    rfl

theorem cell20_82418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 3, 1, 1, 2, 3].length) (baseStart_82418 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82418 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82418 prefixEnd_82418 := by exact prefixLift 82418
  have htrace : WordTrace (prefixWord ++ tailWord_82418) baseStart_82418 baseEnd_82418 := by
    simpa [prefixWord, tailWord_82418, baseEnd_82418] using wordTrace_append hprefix tailTrace_82418
  have hstable : (prefixWord ++ tailWord_82418).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82418).length < 2 ^ (prefixWord ++ tailWord_82418).sum := by decide
  have hdescent : baseEnd_82418 < baseStart_82418 := by decide
  rcases family_descends (prefixWord ++ tailWord_82418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82429 : List Nat := [1, 4, 1, 1, 1, 3, 1, 6, 2]
def baseStart_82429 : Nat := 118140960795 + 82429 * 2 ^ 59
def prefixEnd_82429 : Nat := 4983230072969 + 3 ^ 40 * 82429 * 2
def baseEnd_82429 : Nat := 37622841661833982096375

theorem tailTrace_82429 : CollatzResearch.WordTrace tailWord_82429 prefixEnd_82429 37622841661833982096375 := by
  unfold tailWord_82429
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006432618381285597522341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2004288412254190398348227 3006432618381285597522341)
  ·
    refine ⟨563706115946491049535439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3006432618381285597522341 563706115946491049535439)
    ·
      refine ⟨845559173919736574303159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 563706115946491049535439 845559173919736574303159)
      ·
        refine ⟨1268338760879604861454739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 845559173919736574303159 1268338760879604861454739)
        ·
          refine ⟨1902508141319407292182109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1268338760879604861454739 1902508141319407292182109)
          ·
            refine ⟨713440552994777734568291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1902508141319407292182109 713440552994777734568291)
            ·
              refine ⟨1070160829492166601852437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 713440552994777734568291 1070160829492166601852437)
              ·
                refine ⟨50163788882445309461833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1070160829492166601852437 50163788882445309461833)
                ·
                  refine ⟨37622841661833982096375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50163788882445309461833 37622841661833982096375)
                  ·
                    rfl

theorem cell20_82429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 6, 2].length) (baseStart_82429 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82429 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82429 prefixEnd_82429 := by exact prefixLift 82429
  have htrace : WordTrace (prefixWord ++ tailWord_82429) baseStart_82429 baseEnd_82429 := by
    simpa [prefixWord, tailWord_82429, baseEnd_82429] using wordTrace_append hprefix tailTrace_82429
  have hstable : (prefixWord ++ tailWord_82429).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82429).length < 2 ^ (prefixWord ++ tailWord_82429).sum := by decide
  have hdescent : baseEnd_82429 < baseStart_82429 := by decide
  rcases family_descends (prefixWord ++ tailWord_82429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82439 : List Nat := [1, 1, 4, 3, 3, 1, 3, 1, 3]
def baseStart_82439 : Nat := 118140960795 + 82439 * 2 ^ 59
def prefixEnd_82439 : Nat := 4983230072969 + 3 ^ 40 * 82439 * 2
def baseEnd_82439 : Nat := 37627405934318391763001

theorem tailTrace_82439 : CollatzResearch.WordTrace tailWord_82439 prefixEnd_82439 37627405934318391763001 := by
  unfold tailWord_82439
  simp only [CollatzResearch.WordTrace]
  refine ⟨3006797348345057305386371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2004531565563371536924247 3006797348345057305386371)
  ·
    refine ⟨4510196022517585958079557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3006797348345057305386371 4510196022517585958079557)
    ·
      refine ⟨845661754222047367139917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4510196022517585958079557 845661754222047367139917)
      ·
        refine ⟨317123157833267762677469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 845661754222047367139917 317123157833267762677469)
        ·
          refine ⟨118921184187475411004051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 317123157833267762677469 118921184187475411004051)
          ·
            refine ⟨178381776281213116506077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 118921184187475411004051 178381776281213116506077)
            ·
              refine ⟨66893166105454918689779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 178381776281213116506077 66893166105454918689779)
              ·
                refine ⟨100339749158182378034669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 66893166105454918689779 100339749158182378034669)
                ·
                  refine ⟨37627405934318391763001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100339749158182378034669 37627405934318391763001)
                  ·
                    rfl

theorem cell20_82439_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 3, 1, 3].length) (baseStart_82439 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82439 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82439 prefixEnd_82439 := by exact prefixLift 82439
  have htrace : WordTrace (prefixWord ++ tailWord_82439) baseStart_82439 baseEnd_82439 := by
    simpa [prefixWord, tailWord_82439, baseEnd_82439] using wordTrace_append hprefix tailTrace_82439
  have hstable : (prefixWord ++ tailWord_82439).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82439).length < 2 ^ (prefixWord ++ tailWord_82439).sum := by decide
  have hdescent : baseEnd_82439 < baseStart_82439 := by decide
  rcases family_descends (prefixWord ++ tailWord_82439) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82474 : List Nat := [3, 1, 4, 1, 1, 4, 6]
def baseStart_82474 : Nat := 118140960795 + 82474 * 2 ^ 59
def prefixEnd_82474 : Nat := 4983230072969 + 3 ^ 40 * 82474 * 2
def baseEnd_82474 : Nat := 4182597876445980621799

theorem tailTrace_82474 : CollatzResearch.WordTrace tailWord_82474 prefixEnd_82474 4182597876445980621799 := by
  unfold tailWord_82474
  simp only [CollatzResearch.WordTrace]
  refine ⟨752018475804564570727619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2005382602145505521940317 752018475804564570727619)
  ·
    refine ⟨1128027713706846856091429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 752018475804564570727619 1128027713706846856091429)
    ·
      refine ⟨211505196320033785517143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1128027713706846856091429 211505196320033785517143)
      ·
        refine ⟨317257794480050678275715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 211505196320033785517143 317257794480050678275715)
        ·
          refine ⟨475886691720076017413573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 317257794480050678275715 475886691720076017413573)
          ·
            refine ⟨89228754697514253265045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 475886691720076017413573 89228754697514253265045)
            ·
              refine ⟨4182597876445980621799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89228754697514253265045 4182597876445980621799)
              ·
                rfl

theorem cell20_82474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_82474 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82474 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82474 prefixEnd_82474 := by exact prefixLift 82474
  have htrace : WordTrace (prefixWord ++ tailWord_82474) baseStart_82474 baseEnd_82474 := by
    simpa [prefixWord, tailWord_82474, baseEnd_82474] using wordTrace_append hprefix tailTrace_82474
  have hstable : (prefixWord ++ tailWord_82474).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82474).length < 2 ^ (prefixWord ++ tailWord_82474).sum := by decide
  have hdescent : baseEnd_82474 < baseStart_82474 := by decide
  rcases family_descends (prefixWord ++ tailWord_82474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82495 : List Nat := [1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_82495 : Nat := 118140960795 + 82495 * 2 ^ 59
def prefixEnd_82495 : Nat := 4983230072969 + 3 ^ 40 * 82495 * 2
def baseEnd_82495 : Nat := 12550988620077028632035

theorem tailTrace_82495 : CollatzResearch.WordTrace tailWord_82495 prefixEnd_82495 12550988620077028632035 := by
  unfold tailWord_82495
  simp only [CollatzResearch.WordTrace]
  refine ⟨3008839836142178869424939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2005893224094785912949959 3008839836142178869424939)
  ·
    refine ⟨4513259754213268304137409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3008839836142178869424939 4513259754213268304137409)
    ·
      refine ⟨3384944815659951228103057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4513259754213268304137409 3384944815659951228103057)
      ·
        refine ⟨2538708611744963421077293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3384944815659951228103057 2538708611744963421077293)
        ·
          refine ⟨952015729404361282903985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2538708611744963421077293 952015729404361282903985)
          ·
            refine ⟨714011797053270962177989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 952015729404361282903985 714011797053270962177989)
            ·
              refine ⟨133877211947488305408373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 714011797053270962177989 133877211947488305408373)
              ·
                refine ⟨12550988620077028632035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 133877211947488305408373 12550988620077028632035)
                ·
                  rfl

theorem cell20_82495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_82495 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82495 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82495 prefixEnd_82495 := by exact prefixLift 82495
  have htrace : WordTrace (prefixWord ++ tailWord_82495) baseStart_82495 baseEnd_82495 := by
    simpa [prefixWord, tailWord_82495, baseEnd_82495] using wordTrace_append hprefix tailTrace_82495
  have hstable : (prefixWord ++ tailWord_82495).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82495).length < 2 ^ (prefixWord ++ tailWord_82495).sum := by decide
  have hdescent : baseEnd_82495 < baseStart_82495 := by decide
  rcases family_descends (prefixWord ++ tailWord_82495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82533 : List Nat := [1, 3, 1, 3, 4, 8]
def baseStart_82533 : Nat := 118140960795 + 82533 * 2 ^ 59
def prefixEnd_82533 : Nat := 4983230072969 + 3 ^ 40 * 82533 * 2
def baseEnd_82533 : Nat := 1395196670210068245529

theorem tailTrace_82533 : CollatzResearch.WordTrace tailWord_82533 prefixEnd_82533 1395196670210068245529 := by
  unfold tailWord_82533
  simp only [CollatzResearch.WordTrace]
  refine ⟨3010225810004511359308253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2006817206669674239538835 3010225810004511359308253)
  ·
    refine ⟨1128834678751691759740595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3010225810004511359308253 1128834678751691759740595)
    ·
      refine ⟨1693252018127537639610893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128834678751691759740595 1693252018127537639610893)
      ·
        refine ⟨634969506797826614854085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1693252018127537639610893 634969506797826614854085)
        ·
          refine ⟨119056782524592490285141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 634969506797826614854085 119056782524592490285141)
          ·
            refine ⟨1395196670210068245529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 119056782524592490285141 1395196670210068245529)
            ·
              rfl

theorem cell20_82533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 8].length) (baseStart_82533 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82533 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82533 prefixEnd_82533 := by exact prefixLift 82533
  have htrace : WordTrace (prefixWord ++ tailWord_82533) baseStart_82533 baseEnd_82533 := by
    simpa [prefixWord, tailWord_82533, baseEnd_82533] using wordTrace_append hprefix tailTrace_82533
  have hstable : (prefixWord ++ tailWord_82533).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82533).length < 2 ^ (prefixWord ++ tailWord_82533).sum := by decide
  have hdescent : baseEnd_82533 < baseStart_82533 := by decide
  rcases family_descends (prefixWord ++ tailWord_82533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82540 : List Nat := [2, 2, 1, 1, 3, 1, 2, 3, 5]
def baseStart_82540 : Nat := 118140960795 + 82540 * 2 ^ 59
def prefixEnd_82540 : Nat := 4983230072969 + 3 ^ 40 * 82540 * 2
def baseEnd_82540 : Nat := 37673505086410929395921

theorem tailTrace_82540 : CollatzResearch.WordTrace tailWord_82540 prefixEnd_82540 37673505086410929395921 := by
  unfold tailWord_82540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505240560489575777406537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2006987413986101036542049 1505240560489575777406537)
  ·
    refine ⟨1128930420367181833054903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1505240560489575777406537 1128930420367181833054903)
    ·
      refine ⟨1693395630550772749582355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1128930420367181833054903 1693395630550772749582355)
      ·
        refine ⟨2540093445826159124373533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1693395630550772749582355 2540093445826159124373533)
        ·
          refine ⟨952535042184809671640075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2540093445826159124373533 952535042184809671640075)
          ·
            refine ⟨1428802563277214507460113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 952535042184809671640075 1428802563277214507460113)
            ·
              refine ⟨1071601922457910880595085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1428802563277214507460113 1071601922457910880595085)
              ·
                refine ⟨401850720921716580223157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1071601922457910880595085 401850720921716580223157)
                ·
                  refine ⟨37673505086410929395921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 401850720921716580223157 37673505086410929395921)
                  ·
                    rfl

theorem cell20_82540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 5].length) (baseStart_82540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82540 prefixEnd_82540 := by exact prefixLift 82540
  have htrace : WordTrace (prefixWord ++ tailWord_82540) baseStart_82540 baseEnd_82540 := by
    simpa [prefixWord, tailWord_82540, baseEnd_82540] using wordTrace_append hprefix tailTrace_82540
  have hstable : (prefixWord ++ tailWord_82540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82540).length < 2 ^ (prefixWord ++ tailWord_82540).sum := by decide
  have hdescent : baseEnd_82540 < baseStart_82540 := by decide
  rcases family_descends (prefixWord ++ tailWord_82540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82564 : List Nat := [2, 3, 2, 1, 3, 1, 1, 1, 6]
def baseStart_82564 : Nat := 118140960795 + 82564 * 2 ^ 59
def prefixEnd_82564 : Nat := 4983230072969 + 3 ^ 40 * 82564 * 2
def baseEnd_82564 : Nat := 37684459340373512595823

theorem tailTrace_82564 : CollatzResearch.WordTrace tailWord_82564 prefixEnd_82564 37684459340373512595823 := by
  unfold tailWord_82564
  simp only [CollatzResearch.WordTrace]
  refine ⟨1505678236446101826843373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2007570981928135769124497 1505678236446101826843373)
  ·
    refine ⟨564629338667288185066265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1505678236446101826843373 564629338667288185066265)
    ·
      refine ⟨423472004000466138799699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 564629338667288185066265 423472004000466138799699)
      ·
        refine ⟨635208006000699208199549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423472004000466138799699 635208006000699208199549)
        ·
          refine ⟨238203002250262203074831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 635208006000699208199549 238203002250262203074831)
          ·
            refine ⟨357304503375393304612247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238203002250262203074831 357304503375393304612247)
            ·
              refine ⟨535956755063089956918371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 357304503375393304612247 535956755063089956918371)
              ·
                refine ⟨803935132594634935377557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 535956755063089956918371 803935132594634935377557)
                ·
                  refine ⟨37684459340373512595823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 803935132594634935377557 37684459340373512595823)
                  ·
                    rfl

theorem cell20_82564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 1, 6].length) (baseStart_82564 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82564 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82564 prefixEnd_82564 := by exact prefixLift 82564
  have htrace : WordTrace (prefixWord ++ tailWord_82564) baseStart_82564 baseEnd_82564 := by
    simpa [prefixWord, tailWord_82564, baseEnd_82564] using wordTrace_append hprefix tailTrace_82564
  have hstable : (prefixWord ++ tailWord_82564).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82564).length < 2 ^ (prefixWord ++ tailWord_82564).sum := by decide
  have hdescent : baseEnd_82564 < baseStart_82564 := by decide
  rcases family_descends (prefixWord ++ tailWord_82564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82585 : List Nat := [1, 2, 1, 2, 1, 2, 3, 2, 6]
def baseStart_82585 : Nat := 118140960795 + 82585 * 2 ^ 59
def prefixEnd_82585 : Nat := 4983230072969 + 3 ^ 40 * 82585 * 2
def baseEnd_82585 : Nat := 37694044312590772895737

theorem tailTrace_82585 : CollatzResearch.WordTrace tailWord_82585 prefixEnd_82585 37694044312590772895737 := by
  unfold tailWord_82585
  simp only [CollatzResearch.WordTrace]
  refine ⟨3012122405816124240201209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2008081603877416160134139 3012122405816124240201209)
  ·
    refine ⟨2259091804362093180150907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3012122405816124240201209 2259091804362093180150907)
    ·
      refine ⟨3388637706543139770226361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2259091804362093180150907 3388637706543139770226361)
      ·
        refine ⟨2541478279907354827669771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3388637706543139770226361 2541478279907354827669771)
        ·
          refine ⟨3812217419861032241504657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2541478279907354827669771 3812217419861032241504657)
          ·
            refine ⟨2859163064895774181128493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3812217419861032241504657 2859163064895774181128493)
            ·
              refine ⟨1072186149335915317923185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2859163064895774181128493 1072186149335915317923185)
              ·
                refine ⟨804139612001936488442389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1072186149335915317923185 804139612001936488442389)
                ·
                  refine ⟨37694044312590772895737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 804139612001936488442389 37694044312590772895737)
                  ·
                    rfl

theorem cell20_82585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 2, 6].length) (baseStart_82585 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82585 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82585 prefixEnd_82585 := by exact prefixLift 82585
  have htrace : WordTrace (prefixWord ++ tailWord_82585) baseStart_82585 baseEnd_82585 := by
    simpa [prefixWord, tailWord_82585, baseEnd_82585] using wordTrace_append hprefix tailTrace_82585
  have hstable : (prefixWord ++ tailWord_82585).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82585).length < 2 ^ (prefixWord ++ tailWord_82585).sum := by decide
  have hdescent : baseEnd_82585 < baseStart_82585 := by decide
  rcases family_descends (prefixWord ++ tailWord_82585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82636 : List Nat := [2, 2, 1, 5, 1, 1, 3, 3, 2]
def baseStart_82636 : Nat := 118140960795 + 82636 * 2 ^ 59
def prefixEnd_82636 : Nat := 4983230072969 + 3 ^ 40 * 82636 * 2
def baseEnd_82636 : Nat := 37717322102261262195529

theorem tailTrace_82636 : CollatzResearch.WordTrace tailWord_82636 prefixEnd_82636 37717322102261262195529 := by
  unfold tailWord_82636
  simp only [CollatzResearch.WordTrace]
  refine ⟨1506991264315679975153881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2009321685754239966871841 1506991264315679975153881)
  ·
    refine ⟨1130243448236759981365411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1506991264315679975153881 1130243448236759981365411)
    ·
      refine ⟨1695365172355139972048117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1130243448236759981365411 1695365172355139972048117)
      ·
        refine ⟨158940484908294372379511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 1695365172355139972048117 158940484908294372379511)
        ·
          refine ⟨238410727362441558569267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 158940484908294372379511 238410727362441558569267)
          ·
            refine ⟨357616091043662337853901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 238410727362441558569267 357616091043662337853901)
            ·
              refine ⟨134106034141373376695213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 357616091043662337853901 134106034141373376695213)
              ·
                refine ⟨50289762803015016260705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134106034141373376695213 50289762803015016260705)
                ·
                  refine ⟨37717322102261262195529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50289762803015016260705 37717322102261262195529)
                  ·
                    rfl

theorem cell20_82636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 3, 3, 2].length) (baseStart_82636 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82636 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82636 prefixEnd_82636 := by exact prefixLift 82636
  have htrace : WordTrace (prefixWord ++ tailWord_82636) baseStart_82636 baseEnd_82636 := by
    simpa [prefixWord, tailWord_82636, baseEnd_82636] using wordTrace_append hprefix tailTrace_82636
  have hstable : (prefixWord ++ tailWord_82636).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82636).length < 2 ^ (prefixWord ++ tailWord_82636).sum := by decide
  have hdescent : baseEnd_82636 < baseStart_82636 := by decide
  rcases family_descends (prefixWord ++ tailWord_82636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82647 : List Nat := [1, 1, 3, 2, 1, 6, 6]
def baseStart_82647 : Nat := 118140960795 + 82647 * 2 ^ 59
def prefixEnd_82647 : Nat := 4983230072969 + 3 ^ 40 * 82647 * 2
def baseEnd_82647 : Nat := 4191371422443790314313

theorem tailTrace_82647 : CollatzResearch.WordTrace tailWord_82647 prefixEnd_82647 4191371422443790314313 := by
  unfold tailWord_82647
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014383731591508828958195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2009589154394339219305463 3014383731591508828958195)
  ·
    refine ⟨4521575597387263243437293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3014383731591508828958195 4521575597387263243437293)
    ·
      refine ⟨1695590849020223716288985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4521575597387263243437293 1695590849020223716288985)
      ·
        refine ⟨1271693136765167787216739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1695590849020223716288985 1271693136765167787216739)
        ·
          refine ⟨1907539705147751680825109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1271693136765167787216739 1907539705147751680825109)
          ·
            refine ⟨89415923678800860038677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1907539705147751680825109 89415923678800860038677)
            ·
              refine ⟨4191371422443790314313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 89415923678800860038677 4191371422443790314313)
              ·
                rfl

theorem cell20_82647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 6, 6].length) (baseStart_82647 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82647 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82647 prefixEnd_82647 := by exact prefixLift 82647
  have htrace : WordTrace (prefixWord ++ tailWord_82647) baseStart_82647 baseEnd_82647 := by
    simpa [prefixWord, tailWord_82647, baseEnd_82647] using wordTrace_append hprefix tailTrace_82647
  have hstable : (prefixWord ++ tailWord_82647).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82647).length < 2 ^ (prefixWord ++ tailWord_82647).sum := by decide
  have hdescent : baseEnd_82647 < baseStart_82647 := by decide
  rcases family_descends (prefixWord ++ tailWord_82647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82657 : List Nat := [1, 2, 3, 1, 4, 3, 1, 1, 4]
def baseStart_82657 : Nat := 118140960795 + 82657 * 2 ^ 59
def prefixEnd_82657 : Nat := 4983230072969 + 3 ^ 40 * 82657 * 2
def baseEnd_82657 : Nat := 37726907074478522495443

theorem tailTrace_82657 : CollatzResearch.WordTrace tailWord_82657 prefixEnd_82657 37726907074478522495443 := by
  unfold tailWord_82657
  simp only [CollatzResearch.WordTrace]
  refine ⟨3014748461555280536822225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2009832307703520357881483 3014748461555280536822225)
  ·
    refine ⟨2261061346166460402616669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3014748461555280536822225 2261061346166460402616669)
    ·
      refine ⟨847898004812422650981251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2261061346166460402616669 847898004812422650981251)
      ·
        refine ⟨1271847007218633976471877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 847898004812422650981251 1271847007218633976471877)
        ·
          refine ⟨238471313853493870588477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1271847007218633976471877 238471313853493870588477)
          ·
            refine ⟨89426742695060201470679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238471313853493870588477 89426742695060201470679)
            ·
              refine ⟨134140114042590302206019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89426742695060201470679 134140114042590302206019)
              ·
                refine ⟨201210171063885453309029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 134140114042590302206019 201210171063885453309029)
                ·
                  refine ⟨37726907074478522495443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201210171063885453309029 37726907074478522495443)
                  ·
                    rfl

theorem cell20_82657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4, 3, 1, 1, 4].length) (baseStart_82657 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82657 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82657 prefixEnd_82657 := by exact prefixLift 82657
  have htrace : WordTrace (prefixWord ++ tailWord_82657) baseStart_82657 baseEnd_82657 := by
    simpa [prefixWord, tailWord_82657, baseEnd_82657] using wordTrace_append hprefix tailTrace_82657
  have hstable : (prefixWord ++ tailWord_82657).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82657).length < 2 ^ (prefixWord ++ tailWord_82657).sum := by decide
  have hdescent : baseEnd_82657 < baseStart_82657 := by decide
  rcases family_descends (prefixWord ++ tailWord_82657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82664 : List Nat := [2, 1, 4, 1, 4, 1, 2, 5]
def baseStart_82664 : Nat := 118140960795 + 82664 * 2 ^ 59
def prefixEnd_82664 : Nat := 4983230072969 + 3 ^ 40 * 82664 * 2
def baseEnd_82664 : Nat := 12576700688405869754027

theorem tailTrace_82664 : CollatzResearch.WordTrace tailWord_82664 prefixEnd_82664 12576700688405869754027 := by
  unfold tailWord_82664
  simp only [CollatzResearch.WordTrace]
  refine ⟨1507501886264960366163523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2010002515019947154884697 1507501886264960366163523)
  ·
    refine ⟨2261252829397440549245285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1507501886264960366163523 2261252829397440549245285)
    ·
      refine ⟨423984905512020102983491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2261252829397440549245285 423984905512020102983491)
      ·
        refine ⟨635977358268030154475237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 423984905512020102983491 635977358268030154475237)
        ·
          refine ⟨119245754675255653964107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 635977358268030154475237 119245754675255653964107)
          ·
            refine ⟨178868632012883480946161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119245754675255653964107 178868632012883480946161)
            ·
              refine ⟨134151474009662610709621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 178868632012883480946161 134151474009662610709621)
              ·
                refine ⟨12576700688405869754027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134151474009662610709621 12576700688405869754027)
                ·
                  rfl

theorem cell20_82664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_82664 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82664 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82664 prefixEnd_82664 := by exact prefixLift 82664
  have htrace : WordTrace (prefixWord ++ tailWord_82664) baseStart_82664 baseEnd_82664 := by
    simpa [prefixWord, tailWord_82664, baseEnd_82664] using wordTrace_append hprefix tailTrace_82664
  have hstable : (prefixWord ++ tailWord_82664).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82664).length < 2 ^ (prefixWord ++ tailWord_82664).sum := by decide
  have hdescent : baseEnd_82664 < baseStart_82664 := by decide
  rcases family_descends (prefixWord ++ tailWord_82664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82671 : List Nat := [1, 1, 2, 1, 5, 3, 1, 3, 3]
def baseStart_82671 : Nat := 118140960795 + 82671 * 2 ^ 59
def prefixEnd_82671 : Nat := 4983230072969 + 3 ^ 40 * 82671 * 2
def baseEnd_82671 : Nat := 37733297055956696028719

theorem tailTrace_82671 : CollatzResearch.WordTrace tailWord_82671 prefixEnd_82671 37733297055956696028719 := by
  unfold tailWord_82671
  simp only [CollatzResearch.WordTrace]
  refine ⟨3015259083504560927831867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2010172722336373951887911 3015259083504560927831867)
  ·
    refine ⟨4522888625256841391747801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3015259083504560927831867 4522888625256841391747801)
    ·
      refine ⟨3392166468942631043810851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4522888625256841391747801 3392166468942631043810851)
      ·
        refine ⟨5088249703413946565716277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3392166468942631043810851 5088249703413946565716277)
        ·
          refine ⟨477023409695057490535901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5088249703413946565716277 477023409695057490535901)
          ·
            refine ⟨178883778635646558950963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 477023409695057490535901 178883778635646558950963)
            ·
              refine ⟨268325667953469838426445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 178883778635646558950963 268325667953469838426445)
              ·
                refine ⟨100622125482551189409917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 268325667953469838426445 100622125482551189409917)
                ·
                  refine ⟨37733297055956696028719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100622125482551189409917 37733297055956696028719)
                  ·
                    rfl

theorem cell20_82671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 1, 3, 3].length) (baseStart_82671 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82671 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82671 prefixEnd_82671 := by exact prefixLift 82671
  have htrace : WordTrace (prefixWord ++ tailWord_82671) baseStart_82671 baseEnd_82671 := by
    simpa [prefixWord, tailWord_82671, baseEnd_82671] using wordTrace_append hprefix tailTrace_82671
  have hstable : (prefixWord ++ tailWord_82671).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82671).length < 2 ^ (prefixWord ++ tailWord_82671).sum := by decide
  have hdescent : baseEnd_82671 < baseStart_82671 := by decide
  rcases family_descends (prefixWord ++ tailWord_82671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82678 : List Nat := [5, 1, 1, 1, 1, 2, 2, 1, 6]
def baseStart_82678 : Nat := 118140960795 + 82678 * 2 ^ 59
def prefixEnd_82678 : Nat := 4983230072969 + 3 ^ 40 * 82678 * 2
def baseEnd_82678 : Nat := 37736492046695782795357

theorem tailTrace_82678 : CollatzResearch.WordTrace tailWord_82678 prefixEnd_82678 37736492046695782795357 := by
  unfold tailWord_82678
  simp only [CollatzResearch.WordTrace]
  refine ⟨188469649654950070208543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2010342929652800748891125 188469649654950070208543)
  ·
    refine ⟨282704474482425105312815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 188469649654950070208543 282704474482425105312815)
    ·
      refine ⟨424056711723637657969223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 282704474482425105312815 424056711723637657969223)
      ·
        refine ⟨636085067585456486953835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 424056711723637657969223 636085067585456486953835)
        ·
          refine ⟨954127601378184730430753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 636085067585456486953835 954127601378184730430753)
          ·
            refine ⟨715595701033638547823065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954127601378184730430753 715595701033638547823065)
            ·
              refine ⟨536696775775228910867299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 715595701033638547823065 536696775775228910867299)
              ·
                refine ⟨805045163662843366300949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 536696775775228910867299 805045163662843366300949)
                ·
                  refine ⟨37736492046695782795357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 805045163662843366300949 37736492046695782795357)
                  ·
                    rfl

theorem cell20_82678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_82678 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82678 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82678 prefixEnd_82678 := by exact prefixLift 82678
  have htrace : WordTrace (prefixWord ++ tailWord_82678) baseStart_82678 baseEnd_82678 := by
    simpa [prefixWord, tailWord_82678, baseEnd_82678] using wordTrace_append hprefix tailTrace_82678
  have hstable : (prefixWord ++ tailWord_82678).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82678).length < 2 ^ (prefixWord ++ tailWord_82678).sum := by decide
  have hdescent : baseEnd_82678 < baseStart_82678 := by decide
  rcases family_descends (prefixWord ++ tailWord_82678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82709 : List Nat := [1, 3, 2, 1, 2, 2, 4, 2, 3]
def baseStart_82709 : Nat := 118140960795 + 82709 * 2 ^ 59
def prefixEnd_82709 : Nat := 4983230072969 + 3 ^ 40 * 82709 * 2
def baseEnd_82709 : Nat := 37750641291397452761897

theorem tailTrace_82709 : CollatzResearch.WordTrace tailWord_82709 prefixEnd_82709 37750641291397452761897 := by
  unfold tailWord_82709
  simp only [CollatzResearch.WordTrace]
  refine ⟨3016645057366893417715181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2011096704911262278476787 3016645057366893417715181)
  ·
    refine ⟨1131241896512585031643193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3016645057366893417715181 1131241896512585031643193)
    ·
      refine ⟨848431422384438773732395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1131241896512585031643193 848431422384438773732395)
      ·
        refine ⟨1272647133576658160598593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 848431422384438773732395 1272647133576658160598593)
        ·
          refine ⟨954485350182493620448945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1272647133576658160598593 954485350182493620448945)
          ·
            refine ⟨715864012636870215336709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 954485350182493620448945 715864012636870215336709)
            ·
              refine ⟨134224502369413165375633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 715864012636870215336709 134224502369413165375633)
              ·
                refine ⟨100668376777059874031725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134224502369413165375633 100668376777059874031725)
                ·
                  refine ⟨37750641291397452761897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100668376777059874031725 37750641291397452761897)
                  ·
                    rfl

theorem cell20_82709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 4, 2, 3].length) (baseStart_82709 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82709 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82709 prefixEnd_82709 := by exact prefixLift 82709
  have htrace : WordTrace (prefixWord ++ tailWord_82709) baseStart_82709 baseEnd_82709 := by
    simpa [prefixWord, tailWord_82709, baseEnd_82709] using wordTrace_append hprefix tailTrace_82709
  have hstable : (prefixWord ++ tailWord_82709).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82709).length < 2 ^ (prefixWord ++ tailWord_82709).sum := by decide
  have hdescent : baseEnd_82709 < baseStart_82709 := by decide
  rcases family_descends (prefixWord ++ tailWord_82709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82764 : List Nat := [2, 2, 1, 3, 3, 3, 1, 2, 3]
def baseStart_82764 : Nat := 118140960795 + 82764 * 2 ^ 59
def prefixEnd_82764 : Nat := 4983230072969 + 3 ^ 40 * 82764 * 2
def baseEnd_82764 : Nat := 37775744790061705928339

theorem tailTrace_82764 : CollatzResearch.WordTrace tailWord_82764 prefixEnd_82764 37775744790061705928339 := by
  unfold tailWord_82764
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509325536083818905483673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2012434048111758540644897 1509325536083818905483673)
  ·
    refine ⟨1131994152062864179112755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1509325536083818905483673 1131994152062864179112755)
    ·
      refine ⟨1697991228094296268669133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1131994152062864179112755 1697991228094296268669133)
      ·
        refine ⟨636746710535361100750925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1697991228094296268669133 636746710535361100750925)
        ·
          refine ⟨238780016450760412781597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 636746710535361100750925 238780016450760412781597)
          ·
            refine ⟨89542506169035154793099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 238780016450760412781597 89542506169035154793099)
            ·
              refine ⟨134313759253552732189649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89542506169035154793099 134313759253552732189649)
              ·
                refine ⟨100735319440164549142237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 134313759253552732189649 100735319440164549142237)
                ·
                  refine ⟨37775744790061705928339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100735319440164549142237 37775744790061705928339)
                  ·
                    rfl

theorem cell20_82764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 3, 1, 2, 3].length) (baseStart_82764 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82764 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82764 prefixEnd_82764 := by exact prefixLift 82764
  have htrace : WordTrace (prefixWord ++ tailWord_82764) baseStart_82764 baseEnd_82764 := by
    simpa [prefixWord, tailWord_82764, baseEnd_82764] using wordTrace_append hprefix tailTrace_82764
  have hstable : (prefixWord ++ tailWord_82764).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82764).length < 2 ^ (prefixWord ++ tailWord_82764).sum := by decide
  have hdescent : baseEnd_82764 < baseStart_82764 := by decide
  rcases family_descends (prefixWord ++ tailWord_82764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82792 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 4]
def baseStart_82792 : Nat := 118140960795 + 82792 * 2 ^ 59
def prefixEnd_82792 : Nat := 4983230072969 + 3 ^ 40 * 82792 * 2
def baseEnd_82792 : Nat := 37788524753018052994891

theorem tailTrace_82792 : CollatzResearch.WordTrace tailWord_82792 prefixEnd_82792 37788524753018052994891 := by
  unfold tailWord_82792
  simp only [CollatzResearch.WordTrace]
  refine ⟨1509836158033099296493315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2013114877377465728657753 1509836158033099296493315)
  ·
    refine ⟨2264754237049648944739973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1509836158033099296493315 2264754237049648944739973)
    ·
      refine ⟨424641419446809177138745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2264754237049648944739973 424641419446809177138745)
      ·
        refine ⟨318481064585106882854059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 424641419446809177138745 318481064585106882854059)
        ·
          refine ⟨477721596877660324281089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 318481064585106882854059 477721596877660324281089)
          ·
            refine ⟨358291197658245243210817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 477721596877660324281089 358291197658245243210817)
            ·
              refine ⟨268718398243683932408113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 358291197658245243210817 268718398243683932408113)
              ·
                refine ⟨201538798682762949306085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 268718398243683932408113 201538798682762949306085)
                ·
                  refine ⟨37788524753018052994891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201538798682762949306085 37788524753018052994891)
                  ·
                    rfl

theorem cell20_82792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 4].length) (baseStart_82792 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82792 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82792 prefixEnd_82792 := by exact prefixLift 82792
  have htrace : WordTrace (prefixWord ++ tailWord_82792) baseStart_82792 baseEnd_82792 := by
    simpa [prefixWord, tailWord_82792, baseEnd_82792] using wordTrace_append hprefix tailTrace_82792
  have hstable : (prefixWord ++ tailWord_82792).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82792).length < 2 ^ (prefixWord ++ tailWord_82792).sum := by decide
  have hdescent : baseEnd_82792 < baseStart_82792 := by decide
  rcases family_descends (prefixWord ++ tailWord_82792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82809 : List Nat := [1, 2, 1, 3, 2, 3, 3, 3, 2]
def baseStart_82809 : Nat := 118140960795 + 82809 * 2 ^ 59
def prefixEnd_82809 : Nat := 4983230072969 + 3 ^ 40 * 82809 * 2
def baseEnd_82809 : Nat := 37796284016241549428155

theorem tailTrace_82809 : CollatzResearch.WordTrace tailWord_82809 prefixEnd_82809 37796284016241549428155 := by
  unfold tailWord_82809
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020292357004610496355481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2013528238003073664236987 3020292357004610496355481)
  ·
    refine ⟨2265219267753457872266611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3020292357004610496355481 2265219267753457872266611)
    ·
      refine ⟨3397828901630186808399917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2265219267753457872266611 3397828901630186808399917)
      ·
        refine ⟨1274185838111320053149969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3397828901630186808399917 1274185838111320053149969)
        ·
          refine ⟨955639378583490039862477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274185838111320053149969 955639378583490039862477)
          ·
            refine ⟨358364766968808764948429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 955639378583490039862477 358364766968808764948429)
            ·
              refine ⟨134386787613303286855661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 358364766968808764948429 134386787613303286855661)
              ·
                refine ⟨50395045354988732570873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134386787613303286855661 50395045354988732570873)
                ·
                  refine ⟨37796284016241549428155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50395045354988732570873 37796284016241549428155)
                  ·
                    rfl

theorem cell20_82809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 3, 2].length) (baseStart_82809 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82809 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82809 prefixEnd_82809 := by exact prefixLift 82809
  have htrace : WordTrace (prefixWord ++ tailWord_82809) baseStart_82809 baseEnd_82809 := by
    simpa [prefixWord, tailWord_82809, baseEnd_82809] using wordTrace_append hprefix tailTrace_82809
  have hstable : (prefixWord ++ tailWord_82809).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82809).length < 2 ^ (prefixWord ++ tailWord_82809).sum := by decide
  have hdescent : baseEnd_82809 < baseStart_82809 := by decide
  rcases family_descends (prefixWord ++ tailWord_82809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82813 : List Nat := [1, 4, 1, 1, 2, 1, 2, 2, 6]
def baseStart_82813 : Nat := 118140960795 + 82813 * 2 ^ 59
def prefixEnd_82813 : Nat := 4983230072969 + 3 ^ 40 * 82813 * 2
def baseEnd_82813 : Nat := 37798109725235313294805

theorem tailTrace_82813 : CollatzResearch.WordTrace tailWord_82813 prefixEnd_82813 37798109725235313294805 := by
  unfold tailWord_82813
  simp only [CollatzResearch.WordTrace]
  refine ⟨3020438248990119179501093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2013625499326746119667395 3020438248990119179501093)
  ·
    refine ⟨566332171685647346156455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3020438248990119179501093 566332171685647346156455)
    ·
      refine ⟨849498257528471019234683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 566332171685647346156455 849498257528471019234683)
      ·
        refine ⟨1274247386292706528852025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849498257528471019234683 1274247386292706528852025)
        ·
          refine ⟨955685539719529896639019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1274247386292706528852025 955685539719529896639019)
          ·
            refine ⟨1433528309579294844958529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 955685539719529896639019 1433528309579294844958529)
            ·
              refine ⟨1075146232184471133718897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1433528309579294844958529 1075146232184471133718897)
              ·
                refine ⟨806359674138353350289173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1075146232184471133718897 806359674138353350289173)
                ·
                  refine ⟨37798109725235313294805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 806359674138353350289173 37798109725235313294805)
                  ·
                    rfl

theorem cell20_82813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 2, 6].length) (baseStart_82813 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82813 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82813 prefixEnd_82813 := by exact prefixLift 82813
  have htrace : WordTrace (prefixWord ++ tailWord_82813) baseStart_82813 baseEnd_82813 := by
    simpa [prefixWord, tailWord_82813, baseEnd_82813] using wordTrace_append hprefix tailTrace_82813
  have hstable : (prefixWord ++ tailWord_82813).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82813).length < 2 ^ (prefixWord ++ tailWord_82813).sum := by decide
  have hdescent : baseEnd_82813 < baseStart_82813 := by decide
  rcases family_descends (prefixWord ++ tailWord_82813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82837 : List Nat := [1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_82837 : Nat := 118140960795 + 82837 * 2 ^ 59
def prefixEnd_82837 : Nat := 4983230072969 + 3 ^ 40 * 82837 * 2
def baseEnd_82837 : Nat := 12603021326399298831569

theorem tailTrace_82837 : CollatzResearch.WordTrace tailWord_82837 prefixEnd_82837 12603021326399298831569 := by
  unfold tailWord_82837
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021313600903171278374765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2014209067268780852249843 3021313600903171278374765)
  ·
    refine ⟨1132992600338689229390537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3021313600903171278374765 1132992600338689229390537)
    ·
      refine ⟨849744450254016922042903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1132992600338689229390537 849744450254016922042903)
      ·
        refine ⟨1274616675381025383064355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 849744450254016922042903 1274616675381025383064355)
        ·
          refine ⟨1911925013071538074596533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274616675381025383064355 1911925013071538074596533)
          ·
            refine ⟨179242969975456694493425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1911925013071538074596533 179242969975456694493425)
            ·
              refine ⟨134432227481592520870069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179242969975456694493425 134432227481592520870069)
              ·
                refine ⟨12603021326399298831569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134432227481592520870069 12603021326399298831569)
                ·
                  rfl

theorem cell20_82837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_82837 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82837 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82837 prefixEnd_82837 := by exact prefixLift 82837
  have htrace : WordTrace (prefixWord ++ tailWord_82837) baseStart_82837 baseEnd_82837 := by
    simpa [prefixWord, tailWord_82837, baseEnd_82837] using wordTrace_append hprefix tailTrace_82837
  have hstable : (prefixWord ++ tailWord_82837).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82837).length < 2 ^ (prefixWord ++ tailWord_82837).sum := by decide
  have hdescent : baseEnd_82837 < baseStart_82837 := by decide
  rcases family_descends (prefixWord ++ tailWord_82837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82851 : List Nat := [1, 1, 1, 4, 1, 2, 2, 4, 4]
def baseStart_82851 : Nat := 118140960795 + 82851 * 2 ^ 59
def prefixEnd_82851 : Nat := 4983230072969 + 3 ^ 40 * 82851 * 2
def baseEnd_82851 : Nat := 37815453960676070027983

theorem tailTrace_82851 : CollatzResearch.WordTrace tailWord_82851 prefixEnd_82851 37815453960676070027983 := by
  unfold tailWord_82851
  simp only [CollatzResearch.WordTrace]
  refine ⟨3021824222852451669384407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2014549481901634446256271 3021824222852451669384407)
  ·
    refine ⟨4532736334278677504076611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3021824222852451669384407 4532736334278677504076611)
    ·
      refine ⟨6799104501418016256114917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4532736334278677504076611 6799104501418016256114917)
      ·
        refine ⟨1274832094015878048021547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6799104501418016256114917 1274832094015878048021547)
        ·
          refine ⟨1912248141023817072032321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1274832094015878048021547 1912248141023817072032321)
          ·
            refine ⟨1434186105767862804024241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1912248141023817072032321 1434186105767862804024241)
            ·
              refine ⟨1075639579325897103018181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1434186105767862804024241 1075639579325897103018181)
              ·
                refine ⟨201682421123605706815909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1075639579325897103018181 201682421123605706815909)
                ·
                  refine ⟨37815453960676070027983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201682421123605706815909 37815453960676070027983)
                  ·
                    rfl

theorem cell20_82851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 2, 4, 4].length) (baseStart_82851 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82851 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82851 prefixEnd_82851 := by exact prefixLift 82851
  have htrace : WordTrace (prefixWord ++ tailWord_82851) baseStart_82851 baseEnd_82851 := by
    simpa [prefixWord, tailWord_82851, baseEnd_82851] using wordTrace_append hprefix tailTrace_82851
  have hstable : (prefixWord ++ tailWord_82851).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82851).length < 2 ^ (prefixWord ++ tailWord_82851).sum := by decide
  have hdescent : baseEnd_82851 < baseStart_82851 := by decide
  rcases family_descends (prefixWord ++ tailWord_82851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82906 : List Nat := [3, 1, 1, 2, 4, 2, 1, 2, 4]
def baseStart_82906 : Nat := 118140960795 + 82906 * 2 ^ 59
def prefixEnd_82906 : Nat := 4983230072969 + 3 ^ 40 * 82906 * 2
def baseEnd_82906 : Nat := 37840557459340323194425

theorem tailTrace_82906 : CollatzResearch.WordTrace tailWord_82906 prefixEnd_82906 37840557459340323194425 := by
  unfold tailWord_82906
  simp only [CollatzResearch.WordTrace]
  refine ⟨755957559413299015659143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2015886825102130708424381 755957559413299015659143)
  ·
    refine ⟨1133936339119948523488715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 755957559413299015659143 1133936339119948523488715)
    ·
      refine ⟨1700904508679922785233073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1133936339119948523488715 1700904508679922785233073)
      ·
        refine ⟨1275678381509942088924805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1700904508679922785233073 1275678381509942088924805)
        ·
          refine ⟨239189696533114141673401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1275678381509942088924805 239189696533114141673401)
          ·
            refine ⟨179392272399835606255051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239189696533114141673401 179392272399835606255051)
            ·
              refine ⟨269088408599753409382577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 179392272399835606255051 269088408599753409382577)
              ·
                refine ⟨201816306449815057036933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269088408599753409382577 201816306449815057036933)
                ·
                  refine ⟨37840557459340323194425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 201816306449815057036933 37840557459340323194425)
                  ·
                    rfl

theorem cell20_82906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_82906 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82906 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82906 prefixEnd_82906 := by exact prefixLift 82906
  have htrace : WordTrace (prefixWord ++ tailWord_82906) baseStart_82906 baseEnd_82906 := by
    simpa [prefixWord, tailWord_82906, baseEnd_82906] using wordTrace_append hprefix tailTrace_82906
  have hstable : (prefixWord ++ tailWord_82906).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82906).length < 2 ^ (prefixWord ++ tailWord_82906).sum := by decide
  have hdescent : baseEnd_82906 < baseStart_82906 := by decide
  rcases family_descends (prefixWord ++ tailWord_82906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82930 : List Nat := [3, 2, 1, 5, 1, 1, 7]
def baseStart_82930 : Nat := 118140960795 + 82930 * 2 ^ 59
def prefixEnd_82930 : Nat := 4983230072969 + 3 ^ 40 * 82930 * 2
def baseEnd_82930 : Nat := 4205723523700322932703

theorem tailTrace_82930 : CollatzResearch.WordTrace tailWord_82930 prefixEnd_82930 4205723523700322932703 := by
  unfold tailWord_82930
  simp only [CollatzResearch.WordTrace]
  refine ⟨756176397391562040377561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2016470393044165441006829 756176397391562040377561)
  ·
    refine ⟨567132298043671530283171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 756176397391562040377561 567132298043671530283171)
    ·
      refine ⟨850698447065507295424757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 567132298043671530283171 850698447065507295424757)
      ·
        refine ⟨79752979412391308946071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 850698447065507295424757 79752979412391308946071)
        ·
          refine ⟨119629469118586963419107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79752979412391308946071 119629469118586963419107)
          ·
            refine ⟨179444203677880445128661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119629469118586963419107 179444203677880445128661)
            ·
              refine ⟨4205723523700322932703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 179444203677880445128661 4205723523700322932703)
              ·
                rfl

theorem cell20_82930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_82930 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82930 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82930 prefixEnd_82930 := by exact prefixLift 82930
  have htrace : WordTrace (prefixWord ++ tailWord_82930) baseStart_82930 baseEnd_82930 := by
    simpa [prefixWord, tailWord_82930, baseEnd_82930] using wordTrace_append hprefix tailTrace_82930
  have hstable : (prefixWord ++ tailWord_82930).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82930).length < 2 ^ (prefixWord ++ tailWord_82930).sum := by decide
  have hdescent : baseEnd_82930 < baseStart_82930 := by decide
  rcases family_descends (prefixWord ++ tailWord_82930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82954 : List Nat := [3, 1, 2, 2, 3, 2, 3, 1, 3]
def baseStart_82954 : Nat := 118140960795 + 82954 * 2 ^ 59
def prefixEnd_82954 : Nat := 4983230072969 + 3 ^ 40 * 82954 * 2
def baseEnd_82954 : Nat := 37862465967265489594229

theorem tailTrace_82954 : CollatzResearch.WordTrace tailWord_82954 prefixEnd_82954 37862465967265489594229 := by
  unfold tailWord_82954
  simp only [CollatzResearch.WordTrace]
  refine ⟨756395235369825065095979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2017053960986200173589277 756395235369825065095979)
  ·
    refine ⟨1134592853054737597643969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 756395235369825065095979 1134592853054737597643969)
    ·
      refine ⟨850944639791053198232977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1134592853054737597643969 850944639791053198232977)
      ·
        refine ⟨638208479843289898674733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 850944639791053198232977 638208479843289898674733)
        ·
          refine ⟨239328179941233712003025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 638208479843289898674733 239328179941233712003025)
          ·
            refine ⟨179496134955925284002269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239328179941233712003025 179496134955925284002269)
            ·
              refine ⟨67311050608471981500851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 179496134955925284002269 67311050608471981500851)
              ·
                refine ⟨100966575912707972251277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67311050608471981500851 100966575912707972251277)
                ·
                  refine ⟨37862465967265489594229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 100966575912707972251277 37862465967265489594229)
                  ·
                    rfl

theorem cell20_82954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 3, 1, 3].length) (baseStart_82954 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82954 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82954 prefixEnd_82954 := by exact prefixLift 82954
  have htrace : WordTrace (prefixWord ++ tailWord_82954) baseStart_82954 baseEnd_82954 := by
    simpa [prefixWord, tailWord_82954, baseEnd_82954] using wordTrace_append hprefix tailTrace_82954
  have hstable : (prefixWord ++ tailWord_82954).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82954).length < 2 ^ (prefixWord ++ tailWord_82954).sum := by decide
  have hdescent : baseEnd_82954 < baseStart_82954 := by decide
  rcases family_descends (prefixWord ++ tailWord_82954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82968 : List Nat := [2, 1, 2, 3, 2, 4, 2, 4]
def baseStart_82968 : Nat := 118140960795 + 82968 * 2 ^ 59
def prefixEnd_82968 : Nat := 4983230072969 + 3 ^ 40 * 82968 * 2
def baseEnd_82968 : Nat := 12622951982914554375835

theorem tailTrace_82968 : CollatzResearch.WordTrace tailWord_82968 prefixEnd_82968 12622951982914554375835 := by
  unfold tailWord_82968
  simp only [CollatzResearch.WordTrace]
  refine ⟨1513045781714290325696779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2017394375619053767595705 1513045781714290325696779)
  ·
    refine ⟨2269568672571435488545169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1513045781714290325696779 2269568672571435488545169)
    ·
      refine ⟨1702176504428576616408877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2269568672571435488545169 1702176504428576616408877)
      ·
        refine ⟨638316189160716231153329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1702176504428576616408877 638316189160716231153329)
        ·
          refine ⟨478737141870537173364997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 638316189160716231153329 478737141870537173364997)
          ·
            refine ⟨89763214100725720005937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 478737141870537173364997 89763214100725720005937)
            ·
              refine ⟨67322410575544290004453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89763214100725720005937 67322410575544290004453)
              ·
                refine ⟨12622951982914554375835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67322410575544290004453 12622951982914554375835)
                ·
                  rfl

theorem cell20_82968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 4, 2, 4].length) (baseStart_82968 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82968 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82968 prefixEnd_82968 := by exact prefixLift 82968
  have htrace : WordTrace (prefixWord ++ tailWord_82968) baseStart_82968 baseEnd_82968 := by
    simpa [prefixWord, tailWord_82968, baseEnd_82968] using wordTrace_append hprefix tailTrace_82968
  have hstable : (prefixWord ++ tailWord_82968).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82968).length < 2 ^ (prefixWord ++ tailWord_82968).sum := by decide
  have hdescent : baseEnd_82968 < baseStart_82968 := by decide
  rcases family_descends (prefixWord ++ tailWord_82968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_82978 : List Nat := [3, 3, 1, 1, 1, 5, 1, 3, 2]
def baseStart_82978 : Nat := 118140960795 + 82978 * 2 ^ 59
def prefixEnd_82978 : Nat := 4983230072969 + 3 ^ 40 * 82978 * 2
def baseEnd_82978 : Nat := 37873420221228072794131

theorem tailTrace_82978 : CollatzResearch.WordTrace tailWord_82978 prefixEnd_82978 37873420221228072794131 := by
  unfold tailWord_82978
  simp only [CollatzResearch.WordTrace]
  refine ⟨756614073348088089814397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2017637528928234906171725 756614073348088089814397)
  ·
    refine ⟨283730277505533033680399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 756614073348088089814397 283730277505533033680399)
    ·
      refine ⟨425595416258299550520599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283730277505533033680399 425595416258299550520599)
      ·
        refine ⟨638393124387449325780899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 425595416258299550520599 638393124387449325780899)
        ·
          refine ⟨957589686581173988671349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 638393124387449325780899 957589686581173988671349)
          ·
            refine ⟨89774033116985061437939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 957589686581173988671349 89774033116985061437939)
            ·
              refine ⟨134661049675477592156909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89774033116985061437939 134661049675477592156909)
              ·
                refine ⟨50497893628304097058841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 134661049675477592156909 50497893628304097058841)
                ·
                  refine ⟨37873420221228072794131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50497893628304097058841 37873420221228072794131)
                  ·
                    rfl

theorem cell20_82978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 5, 1, 3, 2].length) (baseStart_82978 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_82978 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_82978 prefixEnd_82978 := by exact prefixLift 82978
  have htrace : WordTrace (prefixWord ++ tailWord_82978) baseStart_82978 baseEnd_82978 := by
    simpa [prefixWord, tailWord_82978, baseEnd_82978] using wordTrace_append hprefix tailTrace_82978
  have hstable : (prefixWord ++ tailWord_82978).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_82978).length < 2 ^ (prefixWord ++ tailWord_82978).sum := by decide
  have hdescent : baseEnd_82978 < baseStart_82978 := by decide
  rcases family_descends (prefixWord ++ tailWord_82978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83006 : List Nat := [4, 2, 1, 3, 1, 2, 2, 5]
def baseStart_83006 : Nat := 118140960795 + 83006 * 2 ^ 59
def prefixEnd_83006 : Nat := 4983230072969 + 3 ^ 40 * 83006 * 2
def baseEnd_83006 : Nat := 12628733394728139953561

theorem tailTrace_83006 : CollatzResearch.WordTrace tailWord_83006 prefixEnd_83006 12628733394728139953561 := by
  unfold tailWord_83006
  simp only [CollatzResearch.WordTrace]
  refine ⟨378434692161364142659609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2018318358193942094184581 378434692161364142659609)
  ·
    refine ⟨283826019121023106994707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 378434692161364142659609 283826019121023106994707)
    ·
      refine ⟨425739028681534660492061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 283826019121023106994707 425739028681534660492061)
      ·
        refine ⟨159652135755575497684523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 425739028681534660492061 159652135755575497684523)
        ·
          refine ⟨239478203633363246526785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159652135755575497684523 239478203633363246526785)
          ·
            refine ⟨179608652725022434895089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 239478203633363246526785 179608652725022434895089)
            ·
              refine ⟨134706489543766826171317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 179608652725022434895089 134706489543766826171317)
              ·
                refine ⟨12628733394728139953561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134706489543766826171317 12628733394728139953561)
                ·
                  rfl

theorem cell20_83006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_83006 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83006 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83006 prefixEnd_83006 := by exact prefixLift 83006
  have htrace : WordTrace (prefixWord ++ tailWord_83006) baseStart_83006 baseEnd_83006 := by
    simpa [prefixWord, tailWord_83006, baseEnd_83006] using wordTrace_append hprefix tailTrace_83006
  have hstable : (prefixWord ++ tailWord_83006).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83006).length < 2 ^ (prefixWord ++ tailWord_83006).sum := by decide
  have hdescent : baseEnd_83006 < baseStart_83006 := by decide
  rcases family_descends (prefixWord ++ tailWord_83006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83009 : List Nat := [1, 2, 5, 1, 3, 2, 2, 1, 3]
def baseStart_83009 : Nat := 118140960795 + 83009 * 2 ^ 59
def prefixEnd_83009 : Nat := 4983230072969 + 3 ^ 40 * 83009 * 2
def baseEnd_83009 : Nat := 37887569465929742760671

theorem tailTrace_83009 : CollatzResearch.WordTrace tailWord_83009 prefixEnd_83009 37887569465929742760671 := by
  unfold tailWord_83009
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027586956280044653636081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018391304186696435757387 3027586956280044653636081)
  ·
    refine ⟨2270690217210033490227061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3027586956280044653636081 2270690217210033490227061)
    ·
      refine ⟨212877207863440639708787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2270690217210033490227061 212877207863440639708787)
      ·
        refine ⟨319315811795160959563181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 212877207863440639708787 319315811795160959563181)
        ·
          refine ⟨119743429423185359836193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 319315811795160959563181 119743429423185359836193)
          ·
            refine ⟨89807572067389019877145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119743429423185359836193 89807572067389019877145)
            ·
              refine ⟨67355679050541764907859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89807572067389019877145 67355679050541764907859)
              ·
                refine ⟨101033518575812647361789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67355679050541764907859 101033518575812647361789)
                ·
                  refine ⟨37887569465929742760671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101033518575812647361789 37887569465929742760671)
                  ·
                    rfl

theorem cell20_83009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 2, 1, 3].length) (baseStart_83009 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83009 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83009 prefixEnd_83009 := by exact prefixLift 83009
  have htrace : WordTrace (prefixWord ++ tailWord_83009) baseStart_83009 baseEnd_83009 := by
    simpa [prefixWord, tailWord_83009, baseEnd_83009] using wordTrace_append hprefix tailTrace_83009
  have hstable : (prefixWord ++ tailWord_83009).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83009).length < 2 ^ (prefixWord ++ tailWord_83009).sum := by decide
  have hdescent : baseEnd_83009 < baseStart_83009 := by decide
  rcases family_descends (prefixWord ++ tailWord_83009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83013 : List Nat := [1, 3, 1, 1, 1, 3, 6, 1, 3]
def baseStart_83013 : Nat := 118140960795 + 83013 * 2 ^ 59
def prefixEnd_83013 : Nat := 4983230072969 + 3 ^ 40 * 83013 * 2
def baseEnd_83013 : Nat := 37889395174923506627321

theorem tailTrace_83013 : CollatzResearch.WordTrace tailWord_83013 prefixEnd_83013 37889395174923506627321 := by
  unfold tailWord_83013
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027732848265553336781693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018488565510368891187795 3027732848265553336781693)
  ·
    refine ⟨1135399818099582501293135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3027732848265553336781693 1135399818099582501293135)
    ·
      refine ⟨1703099727149373751939703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1135399818099582501293135 1703099727149373751939703)
      ·
        refine ⟨2554649590724060627909555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1703099727149373751939703 2554649590724060627909555)
        ·
          refine ⟨3831974386086090941864333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2554649590724060627909555 3831974386086090941864333)
          ·
            refine ⟨1436990394782284103199125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3831974386086090941864333 1436990394782284103199125)
            ·
              refine ⟨67358924755419567337459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 1436990394782284103199125 67358924755419567337459)
              ·
                refine ⟨101038387133129351006189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67358924755419567337459 101038387133129351006189)
                ·
                  refine ⟨37889395174923506627321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101038387133129351006189 37889395174923506627321)
                  ·
                    rfl

theorem cell20_83013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_83013 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83013 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83013 prefixEnd_83013 := by exact prefixLift 83013
  have htrace : WordTrace (prefixWord ++ tailWord_83013) baseStart_83013 baseEnd_83013 := by
    simpa [prefixWord, tailWord_83013, baseEnd_83013] using wordTrace_append hprefix tailTrace_83013
  have hstable : (prefixWord ++ tailWord_83013).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83013).length < 2 ^ (prefixWord ++ tailWord_83013).sum := by decide
  have hdescent : baseEnd_83013 < baseStart_83013 := by decide
  rcases family_descends (prefixWord ++ tailWord_83013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83017 : List Nat := [1, 2, 1, 1, 2, 2, 2, 2, 7]
def baseStart_83017 : Nat := 118140960795 + 83017 * 2 ^ 59
def prefixEnd_83017 : Nat := 4983230072969 + 3 ^ 40 * 83017 * 2
def baseEnd_83017 : Nat := 37891220883917270493971

theorem tailTrace_83017 : CollatzResearch.WordTrace tailWord_83017 prefixEnd_83017 37891220883917270493971 := by
  unfold tailWord_83017
  simp only [CollatzResearch.WordTrace]
  refine ⟨3027878740251062019927305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2018585826834041346618203 3027878740251062019927305)
  ·
    refine ⟨2270909055188296514945479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3027878740251062019927305 2270909055188296514945479)
    ·
      refine ⟨3406363582782444772418219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2270909055188296514945479 3406363582782444772418219)
      ·
        refine ⟨5109545374173667158627329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3406363582782444772418219 5109545374173667158627329)
        ·
          refine ⟨3832159030630250368970497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5109545374173667158627329 3832159030630250368970497)
          ·
            refine ⟨2874119272972687776727873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3832159030630250368970497 2874119272972687776727873)
            ·
              refine ⟨2155589454729515832545905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2874119272972687776727873 2155589454729515832545905)
              ·
                refine ⟨1616692091047136874409429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2155589454729515832545905 1616692091047136874409429)
                ·
                  refine ⟨37891220883917270493971, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1616692091047136874409429 37891220883917270493971)
                  ·
                    rfl

theorem cell20_83017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 2, 7].length) (baseStart_83017 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83017 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83017 prefixEnd_83017 := by exact prefixLift 83017
  have htrace : WordTrace (prefixWord ++ tailWord_83017) baseStart_83017 baseEnd_83017 := by
    simpa [prefixWord, tailWord_83017, baseEnd_83017] using wordTrace_append hprefix tailTrace_83017
  have hstable : (prefixWord ++ tailWord_83017).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83017).length < 2 ^ (prefixWord ++ tailWord_83017).sum := by decide
  have hdescent : baseEnd_83017 < baseStart_83017 := by decide
  rcases family_descends (prefixWord ++ tailWord_83017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83054 : List Nat := [4, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_83054 : Nat := 118140960795 + 83054 * 2 ^ 59
def prefixEnd_83054 : Nat := 4983230072969 + 3 ^ 40 * 83054 * 2
def baseEnd_83054 : Nat := 37908108692109586260487

theorem tailTrace_83054 : CollatzResearch.WordTrace tailWord_83054 prefixEnd_83054 37908108692109586260487 := by
  unfold tailWord_83054
  simp only [CollatzResearch.WordTrace]
  refine ⟨378653530139627167378027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2019485494078011559349477 378653530139627167378027)
  ·
    refine ⟨567980295209440751067041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 378653530139627167378027 567980295209440751067041)
    ·
      refine ⟨425985221407080563300281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 567980295209440751067041 425985221407080563300281)
      ·
        refine ⟨319488916055310422475211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 425985221407080563300281 319488916055310422475211)
        ·
          refine ⟨479233374082965633712817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 319488916055310422475211 479233374082965633712817)
          ·
            refine ⟨359425030562224225284613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 479233374082965633712817 359425030562224225284613)
            ·
              refine ⟨67392193230417042240865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 359425030562224225284613 67392193230417042240865)
              ·
                refine ⟨50544144922812781680649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67392193230417042240865 50544144922812781680649)
                ·
                  refine ⟨37908108692109586260487, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50544144922812781680649 37908108692109586260487)
                  ·
                    rfl

theorem cell20_83054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_83054 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83054 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83054 prefixEnd_83054 := by exact prefixLift 83054
  have htrace : WordTrace (prefixWord ++ tailWord_83054) baseStart_83054 baseEnd_83054 := by
    simpa [prefixWord, tailWord_83054, baseEnd_83054] using wordTrace_append hprefix tailTrace_83054
  have hstable : (prefixWord ++ tailWord_83054).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83054).length < 2 ^ (prefixWord ++ tailWord_83054).sum := by decide
  have hdescent : baseEnd_83054 < baseStart_83054 := by decide
  rcases family_descends (prefixWord ++ tailWord_83054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83061 : List Nat := [1, 3, 4, 3, 1, 2, 1, 5]
def baseStart_83061 : Nat := 118140960795 + 83061 * 2 ^ 59
def prefixEnd_83061 : Nat := 4983230072969 + 3 ^ 40 * 83061 * 2
def baseEnd_83061 : Nat := 12637101227616224342375

theorem tailTrace_83061 : CollatzResearch.WordTrace tailWord_83061 prefixEnd_83061 12637101227616224342375 := by
  unfold tailWord_83061
  simp only [CollatzResearch.WordTrace]
  refine ⟨3029483552091657534529037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2019655701394438356352691 3029483552091657534529037)
  ·
    refine ⟨1136056332034371575448389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3029483552091657534529037 1136056332034371575448389)
    ·
      refine ⟨213010562256444670396573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1136056332034371575448389 213010562256444670396573)
      ·
        refine ⟨79878960846166751398715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 213010562256444670396573 79878960846166751398715)
        ·
          refine ⟨119818441269250127098073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 79878960846166751398715 119818441269250127098073)
          ·
            refine ⟨89863830951937595323555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 119818441269250127098073 89863830951937595323555)
            ·
              refine ⟨134795746427906392985333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 89863830951937595323555 134795746427906392985333)
              ·
                refine ⟨12637101227616224342375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 134795746427906392985333 12637101227616224342375)
                ·
                  rfl

theorem cell20_83061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 2, 1, 5].length) (baseStart_83061 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83061 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83061 prefixEnd_83061 := by exact prefixLift 83061
  have htrace : WordTrace (prefixWord ++ tailWord_83061) baseStart_83061 baseEnd_83061 := by
    simpa [prefixWord, tailWord_83061, baseEnd_83061] using wordTrace_append hprefix tailTrace_83061
  have hstable : (prefixWord ++ tailWord_83061).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83061).length < 2 ^ (prefixWord ++ tailWord_83061).sum := by decide
  have hdescent : baseEnd_83061 < baseStart_83061 := by decide
  rcases family_descends (prefixWord ++ tailWord_83061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83072 : List Nat := [2, 1, 1, 2, 1, 3, 4, 3, 3]
def baseStart_83072 : Nat := 118140960795 + 83072 * 2 ^ 59
def prefixEnd_83072 : Nat := 4983230072969 + 3 ^ 40 * 83072 * 2
def baseEnd_83072 : Nat := 37916324382581523660413

theorem tailTrace_83072 : CollatzResearch.WordTrace tailWord_83072 prefixEnd_83072 37916324382581523660413 := by
  unfold tailWord_83072
  simp only [CollatzResearch.WordTrace]
  refine ⟨1514942377525903206589735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2019923170034537608786313 1514942377525903206589735)
  ·
    refine ⟨2272413566288854809884603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1514942377525903206589735 2272413566288854809884603)
    ·
      refine ⟨3408620349433282214826905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2272413566288854809884603 3408620349433282214826905)
      ·
        refine ⟨2556465262074961661120179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3408620349433282214826905 2556465262074961661120179)
        ·
          refine ⟨3834697893112442491680269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2556465262074961661120179 3834697893112442491680269)
          ·
            refine ⟨1438011709917165934380101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3834697893112442491680269 1438011709917165934380101)
            ·
              refine ⟨269627195609468612696269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1438011709917165934380101 269627195609468612696269)
              ·
                refine ⟨101110198353550729761101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 269627195609468612696269 101110198353550729761101)
                ·
                  refine ⟨37916324382581523660413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101110198353550729761101 37916324382581523660413)
                  ·
                    rfl

theorem cell20_83072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 3, 3].length) (baseStart_83072 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83072 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83072 prefixEnd_83072 := by exact prefixLift 83072
  have htrace : WordTrace (prefixWord ++ tailWord_83072) baseStart_83072 baseEnd_83072 := by
    simpa [prefixWord, tailWord_83072, baseEnd_83072] using wordTrace_append hprefix tailTrace_83072
  have hstable : (prefixWord ++ tailWord_83072).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83072).length < 2 ^ (prefixWord ++ tailWord_83072).sum := by decide
  have hdescent : baseEnd_83072 < baseStart_83072 := by decide
  rcases family_descends (prefixWord ++ tailWord_83072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83103 : List Nat := [1, 1, 2, 6, 2, 1, 7]
def baseStart_83103 : Nat := 118140960795 + 83103 * 2 ^ 59
def prefixEnd_83103 : Nat := 4983230072969 + 3 ^ 40 * 83103 * 2
def baseEnd_83103 : Nat := 4214497069698132625217

theorem tailTrace_83103 : CollatzResearch.WordTrace tailWord_83103 prefixEnd_83103 4214497069698132625217 := by
  unfold tailWord_83103
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031015417939498707557963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2020676945292999138371975 3031015417939498707557963)
  ·
    refine ⟨4546523126909248061336945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3031015417939498707557963 4546523126909248061336945)
    ·
      refine ⟨3409892345181936046002709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4546523126909248061336945 3409892345181936046002709)
      ·
        refine ⟨159838703680403252156377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 3409892345181936046002709 159838703680403252156377)
        ·
          refine ⟨119879027760302439117283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 159838703680403252156377 119879027760302439117283)
          ·
            refine ⟨179818541640453658675925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 119879027760302439117283 179818541640453658675925)
            ·
              refine ⟨4214497069698132625217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 179818541640453658675925 4214497069698132625217)
              ·
                rfl

theorem cell20_83103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 7].length) (baseStart_83103 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83103 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83103 prefixEnd_83103 := by exact prefixLift 83103
  have htrace : WordTrace (prefixWord ++ tailWord_83103) baseStart_83103 baseEnd_83103 := by
    simpa [prefixWord, tailWord_83103, baseEnd_83103] using wordTrace_append hprefix tailTrace_83103
  have hstable : (prefixWord ++ tailWord_83103).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83103).length < 2 ^ (prefixWord ++ tailWord_83103).sum := by decide
  have hdescent : baseEnd_83103 < baseStart_83103 := by decide
  rcases family_descends (prefixWord ++ tailWord_83103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83127 : List Nat := [1, 1, 3, 1, 4, 1, 5, 1, 3]
def baseStart_83127 : Nat := 118140960795 + 83127 * 2 ^ 59
def prefixEnd_83127 : Nat := 4983230072969 + 3 ^ 40 * 83127 * 2
def baseEnd_83127 : Nat := 37941427881245776826855

theorem tailTrace_83127 : CollatzResearch.WordTrace tailWord_83127 prefixEnd_83127 37941427881245776826855 := by
  unfold tailWord_83127
  simp only [CollatzResearch.WordTrace]
  refine ⟨3031890769852550806431635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2021260513235033870954423 3031890769852550806431635)
  ·
    refine ⟨4547836154778826209647453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3031890769852550806431635 4547836154778826209647453)
    ·
      refine ⟨1705438558042059828617795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4547836154778826209647453 1705438558042059828617795)
      ·
        refine ⟨2558157837063089742926693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1705438558042059828617795 2558157837063089742926693)
        ·
          refine ⟨479654594449329326798755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2558157837063089742926693 479654594449329326798755)
          ·
            refine ⟨719481891673993990198133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 479654594449329326798755 719481891673993990198133)
            ·
              refine ⟨67451427344436936581075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 719481891673993990198133 67451427344436936581075)
              ·
                refine ⟨101177141016655404871613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67451427344436936581075 101177141016655404871613)
                ·
                  refine ⟨37941427881245776826855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101177141016655404871613 37941427881245776826855)
                  ·
                    rfl

theorem cell20_83127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 1, 5, 1, 3].length) (baseStart_83127 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83127 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83127 prefixEnd_83127 := by exact prefixLift 83127
  have htrace : WordTrace (prefixWord ++ tailWord_83127) baseStart_83127 baseEnd_83127 := by
    simpa [prefixWord, tailWord_83127, baseEnd_83127] using wordTrace_append hprefix tailTrace_83127
  have hstable : (prefixWord ++ tailWord_83127).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83127).length < 2 ^ (prefixWord ++ tailWord_83127).sum := by decide
  have hdescent : baseEnd_83127 < baseStart_83127 := by decide
  rcases family_descends (prefixWord ++ tailWord_83127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83134 : List Nat := [4, 2, 1, 1, 3, 1, 2, 2, 4]
def baseStart_83134 : Nat := 118140960795 + 83134 * 2 ^ 59
def prefixEnd_83134 : Nat := 4983230072969 + 3 ^ 40 * 83134 * 2
def baseEnd_83134 : Nat := 37944622871984863593493

theorem tailTrace_83134 : CollatzResearch.WordTrace tailWord_83134 prefixEnd_83134 37944622871984863593493 := by
  unfold tailWord_83134
  simp only [CollatzResearch.WordTrace]
  refine ⟨379018260103398875242057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2021430720551460667957637 379018260103398875242057)
  ·
    refine ⟨284263695077549156431543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379018260103398875242057 284263695077549156431543)
    ·
      refine ⟨426395542616323734647315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284263695077549156431543 426395542616323734647315)
      ·
        refine ⟨639593313924485601970973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426395542616323734647315 639593313924485601970973)
        ·
          refine ⟨239847492721682100739115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 639593313924485601970973 239847492721682100739115)
          ·
            refine ⟨359771239082523151108673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 239847492721682100739115 359771239082523151108673)
            ·
              refine ⟨269828429311892363331505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 359771239082523151108673 269828429311892363331505)
              ·
                refine ⟨202371321983919272498629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 269828429311892363331505 202371321983919272498629)
                ·
                  refine ⟨37944622871984863593493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 202371321983919272498629 37944622871984863593493)
                  ·
                    rfl

theorem cell20_83134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_83134 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83134 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83134 prefixEnd_83134 := by exact prefixLift 83134
  have htrace : WordTrace (prefixWord ++ tailWord_83134) baseStart_83134 baseEnd_83134 := by
    simpa [prefixWord, tailWord_83134, baseEnd_83134] using wordTrace_append hprefix tailTrace_83134
  have hstable : (prefixWord ++ tailWord_83134).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83134).length < 2 ^ (prefixWord ++ tailWord_83134).sum := by decide
  have hdescent : baseEnd_83134 < baseStart_83134 := by decide
  rcases family_descends (prefixWord ++ tailWord_83134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83137 : List Nat := [1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_83137 : Nat := 118140960795 + 83137 * 2 ^ 59
def prefixEnd_83137 : Nat := 4983230072969 + 3 ^ 40 * 83137 * 2
def baseEnd_83137 : Nat := 12648664051243395497827

theorem tailTrace_83137 : CollatzResearch.WordTrace tailWord_83137 prefixEnd_83137 12648664051243395497827 := by
  unfold tailWord_83137
  simp only [CollatzResearch.WordTrace]
  refine ⟨3032255499816322514295665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2021503666544215009530443 3032255499816322514295665)
  ·
    refine ⟨2274191624862241885721749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3032255499816322514295665 2274191624862241885721749)
    ·
      refine ⟨106602732415417588393207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 2274191624862241885721749 106602732415417588393207)
      ·
        refine ⟨159904098623126382589811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106602732415417588393207 159904098623126382589811)
        ·
          refine ⟨239856147934689573884717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 159904098623126382589811 239856147934689573884717)
          ·
            refine ⟨89946055475508590206769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 239856147934689573884717 89946055475508590206769)
            ·
              refine ⟨67459541606631442655077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 89946055475508590206769 67459541606631442655077)
              ·
                refine ⟨12648664051243395497827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67459541606631442655077 12648664051243395497827)
                ·
                  rfl

theorem cell20_83137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_83137 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83137 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83137 prefixEnd_83137 := by exact prefixLift 83137
  have htrace : WordTrace (prefixWord ++ tailWord_83137) baseStart_83137 baseEnd_83137 := by
    simpa [prefixWord, tailWord_83137, baseEnd_83137] using wordTrace_append hprefix tailTrace_83137
  have hstable : (prefixWord ++ tailWord_83137).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83137).length < 2 ^ (prefixWord ++ tailWord_83137).sum := by decide
  have hdescent : baseEnd_83137 < baseStart_83137 := by decide
  rcases family_descends (prefixWord ++ tailWord_83137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83172 : List Nat := [2, 3, 1, 1, 1, 2, 2, 6, 2]
def baseStart_83172 : Nat := 118140960795 + 83172 * 2 ^ 59
def prefixEnd_83172 : Nat := 4983230072969 + 3 ^ 40 * 83172 * 2
def baseEnd_83172 : Nat := 37961967107425620326671

theorem tailTrace_83172 : CollatzResearch.WordTrace tailWord_83172 prefixEnd_83172 37961967107425620326671 := by
  unfold tailWord_83172
  simp only [CollatzResearch.WordTrace]
  refine ⟨1516766027344761745909885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2022354703126348994546513 1516766027344761745909885)
  ·
    refine ⟨568787260254285654716207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1516766027344761745909885 568787260254285654716207)
    ·
      refine ⟨853180890381428482074311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 568787260254285654716207 853180890381428482074311)
      ·
        refine ⟨1279771335572142723111467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 853180890381428482074311 1279771335572142723111467)
        ·
          refine ⟨1919657003358214084667201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1279771335572142723111467 1919657003358214084667201)
          ·
            refine ⟨1439742752518660563500401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1919657003358214084667201 1439742752518660563500401)
            ·
              refine ⟨1079807064388995422625301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1439742752518660563500401 1079807064388995422625301)
              ·
                refine ⟨50615956143234160435561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1079807064388995422625301 50615956143234160435561)
                ·
                  refine ⟨37961967107425620326671, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50615956143234160435561 37961967107425620326671)
                  ·
                    rfl

theorem cell20_83172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 6, 2].length) (baseStart_83172 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83172 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83172 prefixEnd_83172 := by exact prefixLift 83172
  have htrace : WordTrace (prefixWord ++ tailWord_83172) baseStart_83172 baseEnd_83172 := by
    simpa [prefixWord, tailWord_83172, baseEnd_83172] using wordTrace_append hprefix tailTrace_83172
  have hstable : (prefixWord ++ tailWord_83172).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83172).length < 2 ^ (prefixWord ++ tailWord_83172).sum := by decide
  have hdescent : baseEnd_83172 < baseStart_83172 := by decide
  rcases family_descends (prefixWord ++ tailWord_83172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83210 : List Nat := [3, 1, 2, 2, 1, 1, 1, 7, 2]
def baseStart_83210 : Nat := 118140960795 + 83210 * 2 ^ 59
def prefixEnd_83210 : Nat := 4983230072969 + 3 ^ 40 * 83210 * 2
def baseEnd_83210 : Nat := 37979311342866377059849

theorem tailTrace_83210 : CollatzResearch.WordTrace tailWord_83210 prefixEnd_83210 37979311342866377059849 := by
  unfold tailWord_83210
  simp only [CollatzResearch.WordTrace]
  refine ⟨758729507137963995425771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2023278685701237321135389 758729507137963995425771)
  ·
    refine ⟨1138094260706945993138657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 758729507137963995425771 1138094260706945993138657)
    ·
      refine ⟨853570695530209494853993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1138094260706945993138657 853570695530209494853993)
      ·
        refine ⟨640178021647657121140495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 853570695530209494853993 640178021647657121140495)
        ·
          refine ⟨960267032471485681710743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640178021647657121140495 960267032471485681710743)
          ·
            refine ⟨1440400548707228522566115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 960267032471485681710743 1440400548707228522566115)
            ·
              refine ⟨2160600823060842783849173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1440400548707228522566115 2160600823060842783849173)
              ·
                refine ⟨50639081790488502746465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 2160600823060842783849173 50639081790488502746465)
                ·
                  refine ⟨37979311342866377059849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50639081790488502746465 37979311342866377059849)
                  ·
                    rfl

theorem cell20_83210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 7, 2].length) (baseStart_83210 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83210 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83210 prefixEnd_83210 := by exact prefixLift 83210
  have htrace : WordTrace (prefixWord ++ tailWord_83210) baseStart_83210 baseEnd_83210 := by
    simpa [prefixWord, tailWord_83210, baseEnd_83210] using wordTrace_append hprefix tailTrace_83210
  have hstable : (prefixWord ++ tailWord_83210).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83210).length < 2 ^ (prefixWord ++ tailWord_83210).sum := by decide
  have hdescent : baseEnd_83210 < baseStart_83210 := by decide
  rcases family_descends (prefixWord ++ tailWord_83210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83224 : List Nat := [2, 1, 2, 3, 1, 3, 1, 4, 3]
def baseStart_83224 : Nat := 118140960795 + 83224 * 2 ^ 59
def prefixEnd_83224 : Nat := 4983230072969 + 3 ^ 40 * 83224 * 2
def baseEnd_83224 : Nat := 37985701324344550593125

theorem tailTrace_83224 : CollatzResearch.WordTrace tailWord_83224 prefixEnd_83224 37985701324344550593125 := by
  unfold tailWord_83224
  simp only [CollatzResearch.WordTrace]
  refine ⟨1517714325250568186356363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2023619100334090915141817 1517714325250568186356363)
  ·
    refine ⟨2276571487875852279534545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1517714325250568186356363 2276571487875852279534545)
    ·
      refine ⟨1707428615906889209650909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2276571487875852279534545 1707428615906889209650909)
      ·
        refine ⟨640285730965083453619091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1707428615906889209650909 640285730965083453619091)
        ·
          refine ⟨960428596447625180428637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640285730965083453619091 960428596447625180428637)
          ·
            refine ⟨360160723667859442660739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 960428596447625180428637 360160723667859442660739)
            ·
              refine ⟨540241085501789163991109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360160723667859442660739 540241085501789163991109)
              ·
                refine ⟨101295203531585468248333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 540241085501789163991109 101295203531585468248333)
                ·
                  refine ⟨37985701324344550593125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101295203531585468248333 37985701324344550593125)
                  ·
                    rfl

theorem cell20_83224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 1, 4, 3].length) (baseStart_83224 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83224 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83224 prefixEnd_83224 := by exact prefixLift 83224
  have htrace : WordTrace (prefixWord ++ tailWord_83224) baseStart_83224 baseEnd_83224 := by
    simpa [prefixWord, tailWord_83224, baseEnd_83224] using wordTrace_append hprefix tailTrace_83224
  have hstable : (prefixWord ++ tailWord_83224).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83224).length < 2 ^ (prefixWord ++ tailWord_83224).sum := by decide
  have hdescent : baseEnd_83224 < baseStart_83224 := by decide
  rcases family_descends (prefixWord ++ tailWord_83224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83230 : List Nat := [4, 3, 2, 1, 3, 1, 1, 5]
def baseStart_83230 : Nat := 118140960795 + 83230 * 2 ^ 59
def prefixEnd_83230 : Nat := 4983230072969 + 3 ^ 40 * 83230 * 2
def baseEnd_83230 : Nat := 12662813295945065464367

theorem tailTrace_83230 : CollatzResearch.WordTrace tailWord_83230 prefixEnd_83230 12662813295945065464367 := by
  unfold tailWord_83230
  simp only [CollatzResearch.WordTrace]
  refine ⟨379455936059924924678893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2023764992319599598287429 379455936059924924678893)
  ·
    refine ⟨142295976022471846754585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 379455936059924924678893 142295976022471846754585)
    ·
      refine ⟨106721982016853885065939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 142295976022471846754585 106721982016853885065939)
      ·
        refine ⟨160082973025280827598909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106721982016853885065939 160082973025280827598909)
        ·
          refine ⟨60031114884480310349591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160082973025280827598909 60031114884480310349591)
          ·
            refine ⟨90046672326720465524387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60031114884480310349591 90046672326720465524387)
            ·
              refine ⟨135070008490080698286581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90046672326720465524387 135070008490080698286581)
              ·
                refine ⟨12662813295945065464367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135070008490080698286581 12662813295945065464367)
                ·
                  rfl

theorem cell20_83230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_83230 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83230 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83230 prefixEnd_83230 := by exact prefixLift 83230
  have htrace : WordTrace (prefixWord ++ tailWord_83230) baseStart_83230 baseEnd_83230 := by
    simpa [prefixWord, tailWord_83230, baseEnd_83230] using wordTrace_append hprefix tailTrace_83230
  have hstable : (prefixWord ++ tailWord_83230).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83230).length < 2 ^ (prefixWord ++ tailWord_83230).sum := by decide
  have hdescent : baseEnd_83230 < baseStart_83230 := by decide
  rcases family_descends (prefixWord ++ tailWord_83230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83234 : List Nat := [3, 3, 1, 1, 4, 2, 1, 5]
def baseStart_83234 : Nat := 118140960795 + 83234 * 2 ^ 59
def prefixEnd_83234 : Nat := 4983230072969 + 3 ^ 40 * 83234 * 2
def baseEnd_83234 : Nat := 12663421865609653419917

theorem tailTrace_83234 : CollatzResearch.WordTrace tailWord_83234 prefixEnd_83234 12663421865609653419917 := by
  unfold tailWord_83234
  simp only [CollatzResearch.WordTrace]
  refine ⟨758948345116227020144189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2023862253643272053717837 758948345116227020144189)
  ·
    refine ⟨284605629418585132554071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 758948345116227020144189 284605629418585132554071)
    ·
      refine ⟨426908444127877698831107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284605629418585132554071 426908444127877698831107)
      ·
        refine ⟨640362666191816548246661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 426908444127877698831107 640362666191816548246661)
        ·
          refine ⟨120067999910965602796249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 640362666191816548246661 120067999910965602796249)
          ·
            refine ⟨90050999933224202097187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120067999910965602796249 90050999933224202097187)
            ·
              refine ⟨135076499899836303145781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90050999933224202097187 135076499899836303145781)
              ·
                refine ⟨12663421865609653419917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135076499899836303145781 12663421865609653419917)
                ·
                  rfl

theorem cell20_83234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 2, 1, 5].length) (baseStart_83234 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83234 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83234 prefixEnd_83234 := by exact prefixLift 83234
  have htrace : WordTrace (prefixWord ++ tailWord_83234) baseStart_83234 baseEnd_83234 := by
    simpa [prefixWord, tailWord_83234, baseEnd_83234] using wordTrace_append hprefix tailTrace_83234
  have hstable : (prefixWord ++ tailWord_83234).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83234).length < 2 ^ (prefixWord ++ tailWord_83234).sum := by decide
  have hdescent : baseEnd_83234 < baseStart_83234 := by decide
  rcases family_descends (prefixWord ++ tailWord_83234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83262 : List Nat := [4, 2, 1, 2, 1, 1, 2, 2, 5]
def baseStart_83262 : Nat := 118140960795 + 83262 * 2 ^ 59
def prefixEnd_83262 : Nat := 4983230072969 + 3 ^ 40 * 83262 * 2
def baseEnd_83262 : Nat := 38003045559785307326303

theorem tailTrace_83262 : CollatzResearch.WordTrace tailWord_83262 prefixEnd_83262 38003045559785307326303 := by
  unfold tailWord_83262
  simp only [CollatzResearch.WordTrace]
  refine ⟨379601828045433607824505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2024543082908979241730693 379601828045433607824505)
  ·
    refine ⟨284701371034075205868379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 379601828045433607824505 284701371034075205868379)
    ·
      refine ⟨427052056551112808802569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 284701371034075205868379 427052056551112808802569)
      ·
        refine ⟨320289042413334606601927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 427052056551112808802569 320289042413334606601927)
        ·
          refine ⟨480433563620001909902891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320289042413334606601927 480433563620001909902891)
          ·
            refine ⟨720650345430002864854337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 480433563620001909902891 720650345430002864854337)
            ·
              refine ⟨540487759072502148640753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 720650345430002864854337 540487759072502148640753)
              ·
                refine ⟨405365819304376611480565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540487759072502148640753 405365819304376611480565)
                ·
                  refine ⟨38003045559785307326303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405365819304376611480565 38003045559785307326303)
                  ·
                    rfl

theorem cell20_83262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_83262 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83262 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83262 prefixEnd_83262 := by exact prefixLift 83262
  have htrace : WordTrace (prefixWord ++ tailWord_83262) baseStart_83262 baseEnd_83262 := by
    simpa [prefixWord, tailWord_83262, baseEnd_83262] using wordTrace_append hprefix tailTrace_83262
  have hstable : (prefixWord ++ tailWord_83262).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83262).length < 2 ^ (prefixWord ++ tailWord_83262).sum := by decide
  have hdescent : baseEnd_83262 < baseStart_83262 := by decide
  rcases family_descends (prefixWord ++ tailWord_83262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83265 : List Nat := [1, 2, 5, 2, 1, 1, 1, 5, 2]
def baseStart_83265 : Nat := 118140960795 + 83265 * 2 ^ 59
def prefixEnd_83265 : Nat := 4983230072969 + 3 ^ 40 * 83265 * 2
def baseEnd_83265 : Nat := 38004414841530630226291

theorem tailTrace_83265 : CollatzResearch.WordTrace tailWord_83265 prefixEnd_83265 38004414841530630226291 := by
  unfold tailWord_83265
  simp only [CollatzResearch.WordTrace]
  refine ⟨3036924043352600374955249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2024616028901733583303499 3036924043352600374955249)
  ·
    refine ⟨2277693032514450281216437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3036924043352600374955249 2277693032514450281216437)
    ·
      refine ⟨213533721798229713864041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 2277693032514450281216437 213533721798229713864041)
      ·
        refine ⟨160150291348672285398031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213533721798229713864041 160150291348672285398031)
        ·
          refine ⟨240225437023008428097047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160150291348672285398031 240225437023008428097047)
          ·
            refine ⟨360338155534512642145571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240225437023008428097047 360338155534512642145571)
            ·
              refine ⟨540507233301768963218357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 360338155534512642145571 540507233301768963218357)
              ·
                refine ⟨50672553122040840301721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 540507233301768963218357 50672553122040840301721)
                ·
                  refine ⟨38004414841530630226291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50672553122040840301721 38004414841530630226291)
                  ·
                    rfl

theorem cell20_83265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_83265 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83265 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83265 prefixEnd_83265 := by exact prefixLift 83265
  have htrace : WordTrace (prefixWord ++ tailWord_83265) baseStart_83265 baseEnd_83265 := by
    simpa [prefixWord, tailWord_83265, baseEnd_83265] using wordTrace_append hprefix tailTrace_83265
  have hstable : (prefixWord ++ tailWord_83265).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83265).length < 2 ^ (prefixWord ++ tailWord_83265).sum := by decide
  have hdescent : baseEnd_83265 < baseStart_83265 := by decide
  rcases family_descends (prefixWord ++ tailWord_83265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83276 : List Nat := [2, 2, 1, 3, 2, 3, 7]
def baseStart_83276 : Nat := 118140960795 + 83276 * 2 ^ 59
def prefixEnd_83276 : Nat := 4983230072969 + 3 ^ 40 * 83276 * 2
def baseEnd_83276 : Nat := 4223270615695942317731

theorem tailTrace_83276 : CollatzResearch.WordTrace tailWord_83276 prefixEnd_83276 4223270615695942317731 := by
  unfold tailWord_83276
  simp only [CollatzResearch.WordTrace]
  refine ⟨1518662623156374626802841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2024883497541832835737121 1518662623156374626802841)
  ·
    refine ⟨1138996967367280970102131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1518662623156374626802841 1138996967367280970102131)
    ·
      refine ⟨1708495451050921455153197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1138996967367280970102131 1708495451050921455153197)
      ·
        refine ⟨640685794144095545682449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1708495451050921455153197 640685794144095545682449)
        ·
          refine ⟨480514345608071659261837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 640685794144095545682449 480514345608071659261837)
          ·
            refine ⟨180192879603026872223189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 480514345608071659261837 180192879603026872223189)
            ·
              refine ⟨4223270615695942317731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 180192879603026872223189 4223270615695942317731)
              ·
                rfl

theorem cell20_83276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 7].length) (baseStart_83276 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83276 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83276 prefixEnd_83276 := by exact prefixLift 83276
  have htrace : WordTrace (prefixWord ++ tailWord_83276) baseStart_83276 baseEnd_83276 := by
    simpa [prefixWord, tailWord_83276, baseEnd_83276] using wordTrace_append hprefix tailTrace_83276
  have hstable : (prefixWord ++ tailWord_83276).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83276).length < 2 ^ (prefixWord ++ tailWord_83276).sum := by decide
  have hdescent : baseEnd_83276 < baseStart_83276 := by decide
  rcases family_descends (prefixWord ++ tailWord_83276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83283 : List Nat := [1, 1, 1, 2, 1, 1, 7, 1, 5]
def baseStart_83283 : Nat := 118140960795 + 83283 * 2 ^ 59
def prefixEnd_83283 : Nat := 4983230072969 + 3 ^ 40 * 83283 * 2
def baseEnd_83283 : Nat := 38012630532002567626217

theorem tailTrace_83283 : CollatzResearch.WordTrace tailWord_83283 prefixEnd_83283 38012630532002567626217 := by
  unfold tailWord_83283
  simp only [CollatzResearch.WordTrace]
  refine ⟨3037580557287389449110503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2025053704858259632740335 3037580557287389449110503)
  ·
    refine ⟨4556370835931084173665755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3037580557287389449110503 4556370835931084173665755)
    ·
      refine ⟨6834556253896626260498633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4556370835931084173665755 6834556253896626260498633)
      ·
        refine ⟨5125917190422469695373975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6834556253896626260498633 5125917190422469695373975)
        ·
          refine ⟨7688875785633704543060963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5125917190422469695373975 7688875785633704543060963)
          ·
            refine ⟨11533313678450556814591445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7688875785633704543060963 11533313678450556814591445)
            ·
              refine ⟨270312039338684925341987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 11533313678450556814591445 270312039338684925341987)
              ·
                refine ⟨405468059008027388012981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 270312039338684925341987 405468059008027388012981)
                ·
                  refine ⟨38012630532002567626217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405468059008027388012981 38012630532002567626217)
                  ·
                    rfl

theorem cell20_83283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 7, 1, 5].length) (baseStart_83283 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83283 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83283 prefixEnd_83283 := by exact prefixLift 83283
  have htrace : WordTrace (prefixWord ++ tailWord_83283) baseStart_83283 baseEnd_83283 := by
    simpa [prefixWord, tailWord_83283, baseEnd_83283] using wordTrace_append hprefix tailTrace_83283
  have hstable : (prefixWord ++ tailWord_83283).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83283).length < 2 ^ (prefixWord ++ tailWord_83283).sum := by decide
  have hdescent : baseEnd_83283 < baseStart_83283 := by decide
  rcases family_descends (prefixWord ++ tailWord_83283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83310 : List Nat := [4, 1, 2, 4, 1, 1, 1, 6]
def baseStart_83310 : Nat := 118140960795 + 83310 * 2 ^ 59
def prefixEnd_83310 : Nat := 4983230072969 + 3 ^ 40 * 83310 * 2
def baseEnd_83310 : Nat := 12674984689236824575369

theorem tailTrace_83310 : CollatzResearch.WordTrace tailWord_83310 prefixEnd_83310 12674984689236824575369 := by
  unfold tailWord_83310
  simp only [CollatzResearch.WordTrace]
  refine ⟨379820666023696632542923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2025710218793048706895589 379820666023696632542923)
  ·
    refine ⟨569730999035544948814385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 379820666023696632542923 569730999035544948814385)
    ·
      refine ⟨427298249276658711610789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 569730999035544948814385 427298249276658711610789)
      ·
        refine ⟨80118421739373508427023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 427298249276658711610789 80118421739373508427023)
        ·
          refine ⟨120177632609060262640535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80118421739373508427023 120177632609060262640535)
          ·
            refine ⟨180266448913590393960803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120177632609060262640535 180266448913590393960803)
            ·
              refine ⟨270399673370385590941205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 180266448913590393960803 270399673370385590941205)
              ·
                refine ⟨12674984689236824575369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270399673370385590941205 12674984689236824575369)
                ·
                  rfl

theorem cell20_83310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 6].length) (baseStart_83310 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83310 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83310 prefixEnd_83310 := by exact prefixLift 83310
  have htrace : WordTrace (prefixWord ++ tailWord_83310) baseStart_83310 baseEnd_83310 := by
    simpa [prefixWord, tailWord_83310, baseEnd_83310] using wordTrace_append hprefix tailTrace_83310
  have hstable : (prefixWord ++ tailWord_83310).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83310).length < 2 ^ (prefixWord ++ tailWord_83310).sum := by decide
  have hdescent : baseEnd_83310 < baseStart_83310 := by decide
  rcases family_descends (prefixWord ++ tailWord_83310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83314 : List Nat := [3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_83314 : Nat := 118140960795 + 83314 * 2 ^ 59
def prefixEnd_83314 : Nat := 4983230072969 + 3 ^ 40 * 83314 * 2
def baseEnd_83314 : Nat := 12675593258901412530919

theorem tailTrace_83314 : CollatzResearch.WordTrace tailWord_83314 prefixEnd_83314 12675593258901412530919 := by
  unfold tailWord_83314
  simp only [CollatzResearch.WordTrace]
  refine ⟨759677805043770435872249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2025807480116721162325997 759677805043770435872249)
  ·
    refine ⟨569758353782827826904187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 759677805043770435872249 569758353782827826904187)
    ·
      refine ⟨854637530674241740356281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 569758353782827826904187 854637530674241740356281)
      ·
        refine ⟨640978148005681305267211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 854637530674241740356281 640978148005681305267211)
        ·
          refine ⟨961467222008521957900817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 640978148005681305267211 961467222008521957900817)
          ·
            refine ⟨721100416506391468425613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 961467222008521957900817 721100416506391468425613)
            ·
              refine ⟨270412656189896800659605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721100416506391468425613 270412656189896800659605)
              ·
                refine ⟨12675593258901412530919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 270412656189896800659605 12675593258901412530919)
                ·
                  rfl

theorem cell20_83314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_83314 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83314 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83314 prefixEnd_83314 := by exact prefixLift 83314
  have htrace : WordTrace (prefixWord ++ tailWord_83314) baseStart_83314 baseEnd_83314 := by
    simpa [prefixWord, tailWord_83314, baseEnd_83314] using wordTrace_append hprefix tailTrace_83314
  have hstable : (prefixWord ++ tailWord_83314).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83314).length < 2 ^ (prefixWord ++ tailWord_83314).sum := by decide
  have hdescent : baseEnd_83314 < baseStart_83314 := by decide
  rcases family_descends (prefixWord ++ tailWord_83314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83321 : List Nat := [1, 2, 1, 3, 2, 1, 3, 2, 5]
def baseStart_83321 : Nat := 118140960795 + 83321 * 2 ^ 59
def prefixEnd_83321 : Nat := 4983230072969 + 3 ^ 40 * 83321 * 2
def baseEnd_83321 : Nat := 38029974767443324359395

theorem tailTrace_83321 : CollatzResearch.WordTrace tailWord_83321 prefixEnd_83321 38029974767443324359395 := by
  unfold tailWord_83321
  simp only [CollatzResearch.WordTrace]
  refine ⟨3038966531149721938993817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2025977687433147959329211 3038966531149721938993817)
  ·
    refine ⟨2279224898362291454245363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3038966531149721938993817 2279224898362291454245363)
    ·
      refine ⟨3418837347543437181368045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279224898362291454245363 3418837347543437181368045)
      ·
        refine ⟨1282064005328788943013017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3418837347543437181368045 1282064005328788943013017)
        ·
          refine ⟨961548003996591707259763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1282064005328788943013017 961548003996591707259763)
          ·
            refine ⟨1442322005994887560889645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 961548003996591707259763 1442322005994887560889645)
            ·
              refine ⟨540870752248082835333617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1442322005994887560889645 540870752248082835333617)
              ·
                refine ⟨405653064186062126500213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 540870752248082835333617 405653064186062126500213)
                ·
                  refine ⟨38029974767443324359395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 405653064186062126500213 38029974767443324359395)
                  ·
                    rfl

theorem cell20_83321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 2, 5].length) (baseStart_83321 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83321 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83321 prefixEnd_83321 := by exact prefixLift 83321
  have htrace : WordTrace (prefixWord ++ tailWord_83321) baseStart_83321 baseEnd_83321 := by
    simpa [prefixWord, tailWord_83321, baseEnd_83321] using wordTrace_append hprefix tailTrace_83321
  have hstable : (prefixWord ++ tailWord_83321).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83321).length < 2 ^ (prefixWord ++ tailWord_83321).sum := by decide
  have hdescent : baseEnd_83321 < baseStart_83321 := by decide
  rcases family_descends (prefixWord ++ tailWord_83321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83328 : List Nat := [2, 1, 1, 2, 1, 2, 1, 4, 6]
def baseStart_83328 : Nat := 118140960795 + 83328 * 2 ^ 59
def prefixEnd_83328 : Nat := 4983230072969 + 3 ^ 40 * 83328 * 2
def baseEnd_83328 : Nat := 38033169758182411126033

theorem tailTrace_83328 : CollatzResearch.WordTrace tailWord_83328 prefixEnd_83328 38033169758182411126033 := by
  unfold tailWord_83328
  simp only [CollatzResearch.WordTrace]
  refine ⟨1519610921062181067249319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2026147894749574756332425 1519610921062181067249319)
  ·
    refine ⟨2279416381593271600873979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1519610921062181067249319 2279416381593271600873979)
    ·
      refine ⟨3419124572389907401310969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2279416381593271600873979 3419124572389907401310969)
      ·
        refine ⟨2564343429292430550983227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3419124572389907401310969 2564343429292430550983227)
        ·
          refine ⟨3846515143938645826474841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2564343429292430550983227 3846515143938645826474841)
          ·
            refine ⟨2884886357953984369856131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3846515143938645826474841 2884886357953984369856131)
            ·
              refine ⟨4327329536930976554784197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2884886357953984369856131 4327329536930976554784197)
              ·
                refine ⟨811374288174558104022037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4327329536930976554784197 811374288174558104022037)
                ·
                  refine ⟨38033169758182411126033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 811374288174558104022037 38033169758182411126033)
                  ·
                    rfl

theorem cell20_83328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 4, 6].length) (baseStart_83328 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83328 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83328 prefixEnd_83328 := by exact prefixLift 83328
  have htrace : WordTrace (prefixWord ++ tailWord_83328) baseStart_83328 baseEnd_83328 := by
    simpa [prefixWord, tailWord_83328, baseEnd_83328] using wordTrace_append hprefix tailTrace_83328
  have hstable : (prefixWord ++ tailWord_83328).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83328).length < 2 ^ (prefixWord ++ tailWord_83328).sum := by decide
  have hdescent : baseEnd_83328 < baseStart_83328 := by decide
  rcases family_descends (prefixWord ++ tailWord_83328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83396 : List Nat := [2, 3, 3, 2, 1, 1, 4, 2, 2]
def baseStart_83396 : Nat := 118140960795 + 83396 * 2 ^ 59
def prefixEnd_83396 : Nat := 4983230072969 + 3 ^ 40 * 83396 * 2
def baseEnd_83396 : Nat := 38064206811076396859089

theorem tailTrace_83396 : CollatzResearch.WordTrace tailWord_83396 prefixEnd_83396 38064206811076396859089 := by
  unfold tailWord_83396
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520851002939004873987021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2027801337252006498649361 1520851002939004873987021)
  ·
    refine ⟨570319126102126827745133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1520851002939004873987021 570319126102126827745133)
    ·
      refine ⟨213869672288297560404425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 570319126102126827745133 213869672288297560404425)
      ·
        refine ⟨160402254216223170303319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 213869672288297560404425 160402254216223170303319)
        ·
          refine ⟨240603381324334755454979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160402254216223170303319 240603381324334755454979)
          ·
            refine ⟨360905071986502133182469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 240603381324334755454979 360905071986502133182469)
            ·
              refine ⟨67669700997469149971713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 360905071986502133182469 67669700997469149971713)
              ·
                refine ⟨50752275748101862478785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67669700997469149971713 50752275748101862478785)
                ·
                  refine ⟨38064206811076396859089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50752275748101862478785 38064206811076396859089)
                  ·
                    rfl

theorem cell20_83396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_83396 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83396 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83396 prefixEnd_83396 := by exact prefixLift 83396
  have htrace : WordTrace (prefixWord ++ tailWord_83396) baseStart_83396 baseEnd_83396 := by
    simpa [prefixWord, tailWord_83396, baseEnd_83396] using wordTrace_append hprefix tailTrace_83396
  have hstable : (prefixWord ++ tailWord_83396).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83396).length < 2 ^ (prefixWord ++ tailWord_83396).sum := by decide
  have hdescent : baseEnd_83396 < baseStart_83396 := by decide
  rcases family_descends (prefixWord ++ tailWord_83396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83400 : List Nat := [2, 1, 3, 1, 3, 1, 3, 4, 2]
def baseStart_83400 : Nat := 118140960795 + 83400 * 2 ^ 59
def prefixEnd_83400 : Nat := 4983230072969 + 3 ^ 40 * 83400 * 2
def baseEnd_83400 : Nat := 38066032520070160725739

theorem tailTrace_83400 : CollatzResearch.WordTrace tailWord_83400 prefixEnd_83400 38066032520070160725739 := by
  unfold tailWord_83400
  simp only [CollatzResearch.WordTrace]
  refine ⟨1520923948931759215559827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2027898598575678954079769 1520923948931759215559827)
  ·
    refine ⟨2281385923397638823339741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1520923948931759215559827 2281385923397638823339741)
    ·
      refine ⟨855519721274114558752403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2281385923397638823339741 855519721274114558752403)
      ·
        refine ⟨1283279581911171838128605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 855519721274114558752403 1283279581911171838128605)
        ·
          refine ⟨481229843216689439298227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1283279581911171838128605 481229843216689439298227)
          ·
            refine ⟨721844764825034158947341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 481229843216689439298227 721844764825034158947341)
            ·
              refine ⟨270691786809387809605253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 721844764825034158947341 270691786809387809605253)
              ·
                refine ⟨50754710026760214300985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 270691786809387809605253 50754710026760214300985)
                ·
                  refine ⟨38066032520070160725739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50754710026760214300985 38066032520070160725739)
                  ·
                    rfl

theorem cell20_83400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 4, 2].length) (baseStart_83400 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83400 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83400 prefixEnd_83400 := by exact prefixLift 83400
  have htrace : WordTrace (prefixWord ++ tailWord_83400) baseStart_83400 baseEnd_83400 := by
    simpa [prefixWord, tailWord_83400, baseEnd_83400] using wordTrace_append hprefix tailTrace_83400
  have hstable : (prefixWord ++ tailWord_83400).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83400).length < 2 ^ (prefixWord ++ tailWord_83400).sum := by decide
  have hdescent : baseEnd_83400 < baseStart_83400 := by decide
  rcases family_descends (prefixWord ++ tailWord_83400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83421 : List Nat := [1, 4, 3, 1, 1, 2, 1, 1, 6]
def baseStart_83421 : Nat := 118140960795 + 83421 * 2 ^ 59
def prefixEnd_83421 : Nat := 4983230072969 + 3 ^ 40 * 83421 * 2
def baseEnd_83421 : Nat := 38075617492287421025653

theorem tailTrace_83421 : CollatzResearch.WordTrace tailWord_83421 prefixEnd_83421 38075617492287421025653 := by
  unfold tailWord_83421
  simp only [CollatzResearch.WordTrace]
  refine ⟨3042613830787439017634117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2028409220524959345089411 3042613830787439017634117)
  ·
    refine ⟨570490093272644815806397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3042613830787439017634117 570490093272644815806397)
    ·
      refine ⟨213933784977241805927399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 570490093272644815806397 213933784977241805927399)
      ·
        refine ⟨320900677465862708891099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 213933784977241805927399 320900677465862708891099)
        ·
          refine ⟨481351016198794063336649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 320900677465862708891099 481351016198794063336649)
          ·
            refine ⟨361013262149095547502487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 481351016198794063336649 361013262149095547502487)
            ·
              refine ⟨541519893223643321253731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 361013262149095547502487 541519893223643321253731)
              ·
                refine ⟨812279839835464981880597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 541519893223643321253731 812279839835464981880597)
                ·
                  refine ⟨38075617492287421025653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 812279839835464981880597 38075617492287421025653)
                  ·
                    rfl

theorem cell20_83421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 1, 1, 6].length) (baseStart_83421 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83421 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83421 prefixEnd_83421 := by exact prefixLift 83421
  have htrace : WordTrace (prefixWord ++ tailWord_83421) baseStart_83421 baseEnd_83421 := by
    simpa [prefixWord, tailWord_83421, baseEnd_83421] using wordTrace_append hprefix tailTrace_83421
  have hstable : (prefixWord ++ tailWord_83421).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83421).length < 2 ^ (prefixWord ++ tailWord_83421).sum := by decide
  have hdescent : baseEnd_83421 < baseStart_83421 := by decide
  rcases family_descends (prefixWord ++ tailWord_83421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83445 : List Nat := [1, 3, 5, 1, 1, 2, 7]
def baseStart_83445 : Nat := 118140960795 + 83445 * 2 ^ 59
def prefixEnd_83445 : Nat := 4983230072969 + 3 ^ 40 * 83445 * 2
def baseEnd_83445 : Nat := 4231841305138889358395

theorem tailTrace_83445 : CollatzResearch.WordTrace tailWord_83445 prefixEnd_83445 4231841305138889358395 := by
  unfold tailWord_83445
  simp only [CollatzResearch.WordTrace]
  refine ⟨3043489182700491116507789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2028992788466994077671859 3043489182700491116507789)
  ·
    refine ⟨1141308443512684168690421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3043489182700491116507789 1141308443512684168690421)
    ·
      refine ⟨106997666579314140814727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 1141308443512684168690421 106997666579314140814727)
      ·
        refine ⟨160496499868971211222091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 106997666579314140814727 160496499868971211222091)
        ·
          refine ⟨240744749803456816833137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 160496499868971211222091 240744749803456816833137)
          ·
            refine ⟨180558562352592612624853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 240744749803456816833137 180558562352592612624853)
            ·
              refine ⟨4231841305138889358395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 180558562352592612624853 4231841305138889358395)
              ·
                rfl

theorem cell20_83445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 2, 7].length) (baseStart_83445 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83445 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83445 prefixEnd_83445 := by exact prefixLift 83445
  have htrace : WordTrace (prefixWord ++ tailWord_83445) baseStart_83445 baseEnd_83445 := by
    simpa [prefixWord, tailWord_83445, baseEnd_83445] using wordTrace_append hprefix tailTrace_83445
  have hstable : (prefixWord ++ tailWord_83445).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83445).length < 2 ^ (prefixWord ++ tailWord_83445).sum := by decide
  have hdescent : baseEnd_83445 < baseStart_83445 := by decide
  rcases family_descends (prefixWord ++ tailWord_83445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83452 : List Nat := [2, 2, 2, 1, 2, 1, 5, 2, 3]
def baseStart_83452 : Nat := 118140960795 + 83452 * 2 ^ 59
def prefixEnd_83452 : Nat := 4983230072969 + 3 ^ 40 * 83452 * 2
def baseEnd_83452 : Nat := 38089766736989090992193

theorem tailTrace_83452 : CollatzResearch.WordTrace tailWord_83452 prefixEnd_83452 38089766736989090992193 := by
  unfold tailWord_83452
  simp only [CollatzResearch.WordTrace]
  refine ⟨1521872246837565656006305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2029162995783420874675073 1521872246837565656006305)
  ·
    refine ⟨1141404185128174242004729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1521872246837565656006305 1141404185128174242004729)
    ·
      refine ⟨856053138846130681503547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1141404185128174242004729 856053138846130681503547)
      ·
        refine ⟨1284079708269196022255321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 856053138846130681503547 1284079708269196022255321)
        ·
          refine ⟨963059781201897016691491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1284079708269196022255321 963059781201897016691491)
          ·
            refine ⟨1444589671802845525037237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 963059781201897016691491 1444589671802845525037237)
            ·
              refine ⟨135430281731516767972241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1444589671802845525037237 135430281731516767972241)
              ·
                refine ⟨101572711298637575979181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135430281731516767972241 101572711298637575979181)
                ·
                  refine ⟨38089766736989090992193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101572711298637575979181 38089766736989090992193)
                  ·
                    rfl

theorem cell20_83452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 5, 2, 3].length) (baseStart_83452 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83452 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83452 prefixEnd_83452 := by exact prefixLift 83452
  have htrace : WordTrace (prefixWord ++ tailWord_83452) baseStart_83452 baseEnd_83452 := by
    simpa [prefixWord, tailWord_83452, baseEnd_83452] using wordTrace_append hprefix tailTrace_83452
  have hstable : (prefixWord ++ tailWord_83452).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83452).length < 2 ^ (prefixWord ++ tailWord_83452).sum := by decide
  have hdescent : baseEnd_83452 < baseStart_83452 := by decide
  rcases family_descends (prefixWord ++ tailWord_83452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83510 : List Nat := [5, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_83510 : Nat := 118140960795 + 83510 * 2 ^ 59
def prefixEnd_83510 : Nat := 4983230072969 + 3 ^ 40 * 83510 * 2
def baseEnd_83510 : Nat := 38116239517398667058623

theorem tailTrace_83510 : CollatzResearch.WordTrace tailWord_83510 prefixEnd_83510 38116239517398667058623 := by
  unfold tailWord_83510
  simp only [CollatzResearch.WordTrace]
  refine ⟨190366245466562951101499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2030573284976671478415989 190366245466562951101499)
  ·
    refine ⟨285549368199844426652249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190366245466562951101499 285549368199844426652249)
    ·
      refine ⟨214162026149883319989187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 285549368199844426652249 214162026149883319989187)
      ·
        refine ⟨321243039224824979983781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 214162026149883319989187 321243039224824979983781)
        ·
          refine ⟨60233069854654683746959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 321243039224824979983781 60233069854654683746959)
          ·
            refine ⟨90349604781982025620439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60233069854654683746959 90349604781982025620439)
            ·
              refine ⟨135524407172973038430659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90349604781982025620439 135524407172973038430659)
              ·
                refine ⟨203286610759459557645989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135524407172973038430659 203286610759459557645989)
                ·
                  refine ⟨38116239517398667058623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203286610759459557645989 38116239517398667058623)
                  ·
                    rfl

theorem cell20_83510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_83510 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83510 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83510 prefixEnd_83510 := by exact prefixLift 83510
  have htrace : WordTrace (prefixWord ++ tailWord_83510) baseStart_83510 baseEnd_83510 := by
    simpa [prefixWord, tailWord_83510, baseEnd_83510] using wordTrace_append hprefix tailTrace_83510
  have hstable : (prefixWord ++ tailWord_83510).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83510).length < 2 ^ (prefixWord ++ tailWord_83510).sum := by decide
  have hdescent : baseEnd_83510 < baseStart_83510 := by decide
  rcases family_descends (prefixWord ++ tailWord_83510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83511 : List Nat := [1, 1, 3, 1, 2, 4, 2, 1, 5]
def baseStart_83511 : Nat := 118140960795 + 83511 * 2 ^ 59
def prefixEnd_83511 : Nat := 4983230072969 + 3 ^ 40 * 83511 * 2
def baseEnd_83511 : Nat := 38116695944647108025285

theorem tailTrace_83511 : CollatzResearch.WordTrace tailWord_83511 prefixEnd_83511 38116695944647108025285 := by
  unfold tailWord_83511
  simp only [CollatzResearch.WordTrace]
  refine ⟨3045896400461384388410387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2030597600307589592273591 3045896400461384388410387)
  ·
    refine ⟨4568844600692076582615581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3045896400461384388410387 4568844600692076582615581)
    ·
      refine ⟨1713316725259528718480843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4568844600692076582615581 1713316725259528718480843)
      ·
        refine ⟨2569975087889293077721265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1713316725259528718480843 2569975087889293077721265)
        ·
          refine ⟨1927481315916969808290949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2569975087889293077721265 1927481315916969808290949)
          ·
            refine ⟨361402746734431839054553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1927481315916969808290949 361402746734431839054553)
            ·
              refine ⟨271052060050823879290915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 361402746734431839054553 271052060050823879290915)
              ·
                refine ⟨406578090076235818936373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 271052060050823879290915 406578090076235818936373)
                ·
                  refine ⟨38116695944647108025285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 406578090076235818936373 38116695944647108025285)
                  ·
                    rfl

theorem cell20_83511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 2, 1, 5].length) (baseStart_83511 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83511 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83511 prefixEnd_83511 := by exact prefixLift 83511
  have htrace : WordTrace (prefixWord ++ tailWord_83511) baseStart_83511 baseEnd_83511 := by
    simpa [prefixWord, tailWord_83511, baseEnd_83511] using wordTrace_append hprefix tailTrace_83511
  have hstable : (prefixWord ++ tailWord_83511).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83511).length < 2 ^ (prefixWord ++ tailWord_83511).sum := by decide
  have hdescent : baseEnd_83511 < baseStart_83511 := by decide
  rcases family_descends (prefixWord ++ tailWord_83511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83565 : List Nat := [1, 5, 1, 1, 5, 1, 2, 2, 2]
def baseStart_83565 : Nat := 118140960795 + 83565 * 2 ^ 59
def prefixEnd_83565 : Nat := 4983230072969 + 3 ^ 40 * 83565 * 2
def baseEnd_83565 : Nat := 38141343016062920225065

theorem tailTrace_83565 : CollatzResearch.WordTrace tailWord_83565 prefixEnd_83565 38141343016062920225065 := by
  unfold tailWord_83565
  simp only [CollatzResearch.WordTrace]
  refine ⟨3047865942265751610876149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2031910628177167740584099 3047865942265751610876149)
  ·
    refine ⟨285737432087414213519639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3047865942265751610876149 285737432087414213519639)
    ·
      refine ⟨428606148131121320279459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 285737432087414213519639 428606148131121320279459)
      ·
        refine ⟨642909222196681980419189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 428606148131121320279459 642909222196681980419189)
        ·
          refine ⟨60272739580938935664299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 642909222196681980419189 60272739580938935664299)
          ·
            refine ⟨90409109371408403496449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60272739580938935664299 90409109371408403496449)
            ·
              refine ⟨67806832028556302622337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90409109371408403496449 67806832028556302622337)
              ·
                refine ⟨50855124021417226966753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 67806832028556302622337 50855124021417226966753)
                ·
                  refine ⟨38141343016062920225065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50855124021417226966753 38141343016062920225065)
                  ·
                    rfl

theorem cell20_83565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 5, 1, 2, 2, 2].length) (baseStart_83565 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83565 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83565 prefixEnd_83565 := by exact prefixLift 83565
  have htrace : WordTrace (prefixWord ++ tailWord_83565) baseStart_83565 baseEnd_83565 := by
    simpa [prefixWord, tailWord_83565, baseEnd_83565] using wordTrace_append hprefix tailTrace_83565
  have hstable : (prefixWord ++ tailWord_83565).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83565).length < 2 ^ (prefixWord ++ tailWord_83565).sum := by decide
  have hdescent : baseEnd_83565 < baseStart_83565 := by decide
  rcases family_descends (prefixWord ++ tailWord_83565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83624 : List Nat := [2, 1, 7, 1, 1, 1, 2, 1, 4]
def baseStart_83624 : Nat := 118140960795 + 83624 * 2 ^ 59
def prefixEnd_83624 : Nat := 4983230072969 + 3 ^ 40 * 83624 * 2
def baseEnd_83624 : Nat := 38168272223720937258157

theorem tailTrace_83624 : CollatzResearch.WordTrace tailWord_83624 prefixEnd_83624 38168272223720937258157 := by
  unfold tailWord_83624
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525008924526002343636963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2033345232701336458182617 1525008924526002343636963)
  ·
    refine ⟨2287513386789003515455445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525008924526002343636963 2287513386789003515455445)
    ·
      refine ⟨53613595002867269893487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 2287513386789003515455445 53613595002867269893487)
      ·
        refine ⟨80420392504300904840231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53613595002867269893487 80420392504300904840231)
        ·
          refine ⟨120630588756451357260347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80420392504300904840231 120630588756451357260347)
          ·
            refine ⟨180945883134677035890521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120630588756451357260347 180945883134677035890521)
            ·
              refine ⟨135709412351007776917891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 180945883134677035890521 135709412351007776917891)
              ·
                refine ⟨203564118526511665376837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135709412351007776917891 203564118526511665376837)
                ·
                  refine ⟨38168272223720937258157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203564118526511665376837 38168272223720937258157)
                  ·
                    rfl

theorem cell20_83624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 1, 1, 2, 1, 4].length) (baseStart_83624 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83624 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83624 prefixEnd_83624 := by exact prefixLift 83624
  have htrace : WordTrace (prefixWord ++ tailWord_83624) baseStart_83624 baseEnd_83624 := by
    simpa [prefixWord, tailWord_83624, baseEnd_83624] using wordTrace_append hprefix tailTrace_83624
  have hstable : (prefixWord ++ tailWord_83624).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83624).length < 2 ^ (prefixWord ++ tailWord_83624).sum := by decide
  have hdescent : baseEnd_83624 < baseStart_83624 := by decide
  rcases family_descends (prefixWord ++ tailWord_83624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83632 : List Nat := [2, 1, 1, 1, 2, 1, 5, 3, 4]
def baseStart_83632 : Nat := 118140960795 + 83632 * 2 ^ 59
def prefixEnd_83632 : Nat := 4983230072969 + 3 ^ 40 * 83632 * 2
def baseEnd_83632 : Nat := 38171923641708464991457

theorem tailTrace_83632 : CollatzResearch.WordTrace tailWord_83632 prefixEnd_83632 38171923641708464991457 := by
  unfold tailWord_83632
  simp only [CollatzResearch.WordTrace]
  refine ⟨1525154816511511026782575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2033539755348681369043433 1525154816511511026782575)
  ·
    refine ⟨2287732224767266540173863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1525154816511511026782575 2287732224767266540173863)
    ·
      refine ⟨3431598337150899810260795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2287732224767266540173863 3431598337150899810260795)
      ·
        refine ⟨5147397505726349715391193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3431598337150899810260795 5147397505726349715391193)
        ·
          refine ⟨3860548129294762286543395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5147397505726349715391193 3860548129294762286543395)
          ·
            refine ⟨5790822193942143429815093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3860548129294762286543395 5790822193942143429815093)
            ·
              refine ⟨542889580682075946545165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5790822193942143429815093 542889580682075946545165)
              ·
                refine ⟨203583592755778479954437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 542889580682075946545165 203583592755778479954437)
                ·
                  refine ⟨38171923641708464991457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203583592755778479954437 38171923641708464991457)
                  ·
                    rfl

theorem cell20_83632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 5, 3, 4].length) (baseStart_83632 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83632 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83632 prefixEnd_83632 := by exact prefixLift 83632
  have htrace : WordTrace (prefixWord ++ tailWord_83632) baseStart_83632 baseEnd_83632 := by
    simpa [prefixWord, tailWord_83632, baseEnd_83632] using wordTrace_append hprefix tailTrace_83632
  have hstable : (prefixWord ++ tailWord_83632).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83632).length < 2 ^ (prefixWord ++ tailWord_83632).sum := by decide
  have hdescent : baseEnd_83632 < baseStart_83632 := by decide
  rcases family_descends (prefixWord ++ tailWord_83632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83683 : List Nat := [1, 1, 1, 7, 3, 1, 1, 1, 4]
def baseStart_83683 : Nat := 118140960795 + 83683 * 2 ^ 59
def prefixEnd_83683 : Nat := 4983230072969 + 3 ^ 40 * 83683 * 2
def baseEnd_83683 : Nat := 38195201431378954291249

theorem tailTrace_83683 : CollatzResearch.WordTrace tailWord_83683 prefixEnd_83683 38195201431378954291249 := by
  unfold tailWord_83683
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052169755838257763671703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2034779837225505175781135 3052169755838257763671703)
  ·
    refine ⟨4578254633757386645507555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3052169755838257763671703 4578254633757386645507555)
    ·
      refine ⟨6867381950636079968261333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4578254633757386645507555 6867381950636079968261333)
      ·
        refine ⟨160954264468033124256125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 6867381950636079968261333 160954264468033124256125)
        ·
          refine ⟨60357849175512421596047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 160954264468033124256125 60357849175512421596047)
          ·
            refine ⟨90536773763268632394071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60357849175512421596047 90536773763268632394071)
            ·
              refine ⟨135805160644902948591107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90536773763268632394071 135805160644902948591107)
              ·
                refine ⟨203707740967354422886661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 135805160644902948591107 203707740967354422886661)
                ·
                  refine ⟨38195201431378954291249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203707740967354422886661 38195201431378954291249)
                  ·
                    rfl

theorem cell20_83683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 3, 1, 1, 1, 4].length) (baseStart_83683 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83683 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83683 prefixEnd_83683 := by exact prefixLift 83683
  have htrace : WordTrace (prefixWord ++ tailWord_83683) baseStart_83683 baseEnd_83683 := by
    simpa [prefixWord, tailWord_83683, baseEnd_83683] using wordTrace_append hprefix tailTrace_83683
  have hstable : (prefixWord ++ tailWord_83683).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83683).length < 2 ^ (prefixWord ++ tailWord_83683).sum := by decide
  have hdescent : baseEnd_83683 < baseStart_83683 := by decide
  rcases family_descends (prefixWord ++ tailWord_83683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83694 : List Nat := [4, 1, 2, 1, 1, 2, 4, 5]
def baseStart_83694 : Nat := 118140960795 + 83694 * 2 ^ 59
def prefixEnd_83694 : Nat := 4983230072969 + 3 ^ 40 * 83694 * 2
def baseEnd_83694 : Nat := 12733407377037268308179

theorem tailTrace_83694 : CollatzResearch.WordTrace tailWord_83694 prefixEnd_83694 12733407377037268308179 := by
  unfold tailWord_83694
  simp only [CollatzResearch.WordTrace]
  refine ⟨381571369849800830290267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2035047305865604428214757 381571369849800830290267)
  ·
    refine ⟨572357054774701245435401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 381571369849800830290267 572357054774701245435401)
    ·
      refine ⟨429267791081025934076551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 572357054774701245435401 429267791081025934076551)
      ·
        refine ⟨643901686621538901114827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429267791081025934076551 643901686621538901114827)
        ·
          refine ⟨965852529932308351672241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 643901686621538901114827 965852529932308351672241)
          ·
            refine ⟨724389397449231263754181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 965852529932308351672241 724389397449231263754181)
            ·
              refine ⟨135823012021730861953909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 724389397449231263754181 135823012021730861953909)
              ·
                refine ⟨12733407377037268308179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 135823012021730861953909 12733407377037268308179)
                ·
                  rfl

theorem cell20_83694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 4, 5].length) (baseStart_83694 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83694 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83694 prefixEnd_83694 := by exact prefixLift 83694
  have htrace : WordTrace (prefixWord ++ tailWord_83694) baseStart_83694 baseEnd_83694 := by
    simpa [prefixWord, tailWord_83694, baseEnd_83694] using wordTrace_append hprefix tailTrace_83694
  have hstable : (prefixWord ++ tailWord_83694).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83694).length < 2 ^ (prefixWord ++ tailWord_83694).sum := by decide
  have hdescent : baseEnd_83694 < baseStart_83694 := by decide
  rcases family_descends (prefixWord ++ tailWord_83694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83697 : List Nat := [1, 2, 2, 2, 2, 5, 2, 1, 3]
def baseStart_83697 : Nat := 118140960795 + 83697 * 2 ^ 59
def prefixEnd_83697 : Nat := 4983230072969 + 3 ^ 40 * 83697 * 2
def baseEnd_83697 : Nat := 38201591412857127824525

theorem tailTrace_83697 : CollatzResearch.WordTrace tailWord_83697 prefixEnd_83697 38201591412857127824525 := by
  unfold tailWord_83697
  simp only [CollatzResearch.WordTrace]
  refine ⟨3052680377787538154681345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2035120251858358769787563 3052680377787538154681345)
  ·
    refine ⟨2289510283340653616011009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3052680377787538154681345 2289510283340653616011009)
    ·
      refine ⟨1717132712505490212008257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2289510283340653616011009 1717132712505490212008257)
      ·
        refine ⟨1287849534379117659006193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1717132712505490212008257 1287849534379117659006193)
        ·
          refine ⟨965887150784338244254645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1287849534379117659006193 965887150784338244254645)
          ·
            refine ⟨90551920386031710398873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 965887150784338244254645 90551920386031710398873)
            ·
              refine ⟨67913940289523782799155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90551920386031710398873 67913940289523782799155)
              ·
                refine ⟨101870910434285674198733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 67913940289523782799155 101870910434285674198733)
                ·
                  refine ⟨38201591412857127824525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101870910434285674198733 38201591412857127824525)
                  ·
                    rfl

theorem cell20_83697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 5, 2, 1, 3].length) (baseStart_83697 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83697 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83697 prefixEnd_83697 := by exact prefixLift 83697
  have htrace : WordTrace (prefixWord ++ tailWord_83697) baseStart_83697 baseEnd_83697 := by
    simpa [prefixWord, tailWord_83697, baseEnd_83697] using wordTrace_append hprefix tailTrace_83697
  have hstable : (prefixWord ++ tailWord_83697).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83697).length < 2 ^ (prefixWord ++ tailWord_83697).sum := by decide
  have hdescent : baseEnd_83697 < baseStart_83697 := by decide
  rcases family_descends (prefixWord ++ tailWord_83697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83708 : List Nat := [2, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_83708 : Nat := 118140960795 + 83708 * 2 ^ 59
def prefixEnd_83708 : Nat := 4983230072969 + 3 ^ 40 * 83708 * 2
def baseEnd_83708 : Nat := 38206612112589978457813

theorem tailTrace_83708 : CollatzResearch.WordTrace tailWord_83708 prefixEnd_83708 38206612112589978457813 := by
  unfold tailWord_83708
  simp only [CollatzResearch.WordTrace]
  refine ⟨1526540790373843516665889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2035387720498458022221185 1526540790373843516665889)
  ·
    refine ⟨1144905592780382637499417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1526540790373843516665889 1144905592780382637499417)
    ·
      refine ⟨858679194585286978124563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1144905592780382637499417 858679194585286978124563)
      ·
        refine ⟨1288018791877930467186845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 858679194585286978124563 1288018791877930467186845)
        ·
          refine ⟨483007046954223925195067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1288018791877930467186845 483007046954223925195067)
          ·
            refine ⟨724510570431335887792601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 483007046954223925195067 724510570431335887792601)
            ·
              refine ⟨543382927823501915844451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 724510570431335887792601 543382927823501915844451)
              ·
                refine ⟨815074391735252873766677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 543382927823501915844451 815074391735252873766677)
                ·
                  refine ⟨38206612112589978457813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 815074391735252873766677 38206612112589978457813)
                  ·
                    rfl

theorem cell20_83708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_83708 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83708 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83708 prefixEnd_83708 := by exact prefixLift 83708
  have htrace : WordTrace (prefixWord ++ tailWord_83708) baseStart_83708 baseEnd_83708 := by
    simpa [prefixWord, tailWord_83708, baseEnd_83708] using wordTrace_append hprefix tailTrace_83708
  have hstable : (prefixWord ++ tailWord_83708).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83708).length < 2 ^ (prefixWord ++ tailWord_83708).sum := by decide
  have hdescent : baseEnd_83708 < baseStart_83708 := by decide
  rcases family_descends (prefixWord ++ tailWord_83708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83715 : List Nat := [1, 1, 1, 3, 2, 2, 4, 6]
def baseStart_83715 : Nat := 118140960795 + 83715 * 2 ^ 59
def prefixEnd_83715 : Nat := 4983230072969 + 3 ^ 40 * 83715 * 2
def baseEnd_83715 : Nat := 12736602367776355074817

theorem tailTrace_83715 : CollatzResearch.WordTrace tailWord_83715 prefixEnd_83715 12736602367776355074817 := by
  unfold tailWord_83715
  simp only [CollatzResearch.WordTrace]
  refine ⟨3053336891722327228836599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2035557927814884819224399 3053336891722327228836599)
  ·
    refine ⟨4580005337583490843254899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3053336891722327228836599 4580005337583490843254899)
    ·
      refine ⟨6870008006375236264882349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4580005337583490843254899 6870008006375236264882349)
      ·
        refine ⟨2576253002390713599330881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6870008006375236264882349 2576253002390713599330881)
        ·
          refine ⟨1932189751793035199498161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2576253002390713599330881 1932189751793035199498161)
          ·
            refine ⟨1449142313844776399623621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1932189751793035199498161 1449142313844776399623621)
            ·
              refine ⟨271714183845895574929429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1449142313844776399623621 271714183845895574929429)
              ·
                refine ⟨12736602367776355074817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 271714183845895574929429 12736602367776355074817)
                ·
                  rfl

theorem cell20_83715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 6].length) (baseStart_83715 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83715 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83715 prefixEnd_83715 := by exact prefixLift 83715
  have htrace : WordTrace (prefixWord ++ tailWord_83715) baseStart_83715 baseEnd_83715 := by
    simpa [prefixWord, tailWord_83715, baseEnd_83715] using wordTrace_append hprefix tailTrace_83715
  have hstable : (prefixWord ++ tailWord_83715).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83715).length < 2 ^ (prefixWord ++ tailWord_83715).sum := by decide
  have hdescent : baseEnd_83715 < baseStart_83715 := by decide
  rcases family_descends (prefixWord ++ tailWord_83715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83760 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 9]
def baseStart_83760 : Nat := 118140960795 + 83760 * 2 ^ 59
def prefixEnd_83760 : Nat := 4983230072969 + 3 ^ 40 * 83760 * 2
def baseEnd_83760 : Nat := 38230346329508908724267

theorem tailTrace_83760 : CollatzResearch.WordTrace tailWord_83760 prefixEnd_83760 38230346329508908724267 := by
  unfold tailWord_83760
  simp only [CollatzResearch.WordTrace]
  refine ⟨1527489088279649957112367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2036652117706199942816489 1527489088279649957112367)
  ·
    refine ⟨2291233632419474935668551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1527489088279649957112367 2291233632419474935668551)
    ·
      refine ⟨3436850448629212403502827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2291233632419474935668551 3436850448629212403502827)
      ·
        refine ⟨5155275672943818605254241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3436850448629212403502827 5155275672943818605254241)
        ·
          refine ⟨3866456754707863953940681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5155275672943818605254241 3866456754707863953940681)
          ·
            refine ⟨2899842566030897965455511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3866456754707863953940681 2899842566030897965455511)
            ·
              refine ⟨4349763849046346948183267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2899842566030897965455511 4349763849046346948183267)
              ·
                refine ⟨6524645773569520422274901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4349763849046346948183267 6524645773569520422274901)
                ·
                  refine ⟨38230346329508908724267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 6524645773569520422274901 38230346329508908724267)
                  ·
                    rfl

theorem cell20_83760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 9].length) (baseStart_83760 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83760 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83760 prefixEnd_83760 := by exact prefixLift 83760
  have htrace : WordTrace (prefixWord ++ tailWord_83760) baseStart_83760 baseEnd_83760 := by
    simpa [prefixWord, tailWord_83760, baseEnd_83760] using wordTrace_append hprefix tailTrace_83760
  have hstable : (prefixWord ++ tailWord_83760).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83760).length < 2 ^ (prefixWord ++ tailWord_83760).sum := by decide
  have hdescent : baseEnd_83760 < baseStart_83760 := by decide
  rcases family_descends (prefixWord ++ tailWord_83760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83763 : List Nat := [1, 1, 1, 2, 7, 1, 1, 2, 4]
def baseStart_83763 : Nat := 118140960795 + 83763 * 2 ^ 59
def prefixEnd_83763 : Nat := 4983230072969 + 3 ^ 40 * 83763 * 2
def baseEnd_83763 : Nat := 38231715611254231624255

theorem tailTrace_83763 : CollatzResearch.WordTrace tailWord_83763 prefixEnd_83763 38231715611254231624255 := by
  unfold tailWord_83763
  simp only [CollatzResearch.WordTrace]
  refine ⟨3055087595548431426583943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2036725063698954284389295 3055087595548431426583943)
  ·
    refine ⟨4582631393322647139875915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3055087595548431426583943 4582631393322647139875915)
    ·
      refine ⟨6873947089983970709813873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4582631393322647139875915 6873947089983970709813873)
      ·
        refine ⟨5155460317487978032360405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6873947089983970709813873 5155460317487978032360405)
        ·
          refine ⟨120831101191124485133447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 5155460317487978032360405 120831101191124485133447)
          ·
            refine ⟨181246651786686727700171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120831101191124485133447 181246651786686727700171)
            ·
              refine ⟨271869977680030091550257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 181246651786686727700171 271869977680030091550257)
              ·
                refine ⟨203902483260022568662693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 271869977680030091550257 203902483260022568662693)
                ·
                  refine ⟨38231715611254231624255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 203902483260022568662693 38231715611254231624255)
                  ·
                    rfl

theorem cell20_83763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 1, 2, 4].length) (baseStart_83763 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83763 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83763 prefixEnd_83763 := by exact prefixLift 83763
  have htrace : WordTrace (prefixWord ++ tailWord_83763) baseStart_83763 baseEnd_83763 := by
    simpa [prefixWord, tailWord_83763, baseEnd_83763] using wordTrace_append hprefix tailTrace_83763
  have hstable : (prefixWord ++ tailWord_83763).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83763).length < 2 ^ (prefixWord ++ tailWord_83763).sum := by decide
  have hdescent : baseEnd_83763 < baseStart_83763 := by decide
  rcases family_descends (prefixWord ++ tailWord_83763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83766 : List Nat := [5, 1, 2, 2, 1, 2, 3, 4]
def baseStart_83766 : Nat := 118140960795 + 83766 * 2 ^ 59
def prefixEnd_83766 : Nat := 4983230072969 + 3 ^ 40 * 83766 * 2
def baseEnd_83766 : Nat := 12744361630999851508081

theorem tailTrace_83766 : CollatzResearch.WordTrace tailWord_83766 prefixEnd_83766 12744361630999851508081 := by
  unfold tailWord_83766
  simp only [CollatzResearch.WordTrace]
  refine ⟨190949813408597683683947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2036798009691708625962101 190949813408597683683947)
  ·
    refine ⟨286424720112896525525921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 190949813408597683683947 286424720112896525525921)
    ·
      refine ⟨214818540084672394144441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 286424720112896525525921 214818540084672394144441)
      ·
        refine ⟨161113905063504295608331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 214818540084672394144441 161113905063504295608331)
        ·
          refine ⟨241670857595256443412497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 161113905063504295608331 241670857595256443412497)
          ·
            refine ⟨181253143196442332559373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 241670857595256443412497 181253143196442332559373)
            ·
              refine ⟨67969928698665874709765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181253143196442332559373 67969928698665874709765)
              ·
                refine ⟨12744361630999851508081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 67969928698665874709765 12744361630999851508081)
                ·
                  rfl

theorem cell20_83766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 2, 3, 4].length) (baseStart_83766 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83766 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83766 prefixEnd_83766 := by exact prefixLift 83766
  have htrace : WordTrace (prefixWord ++ tailWord_83766) baseStart_83766 baseEnd_83766 := by
    simpa [prefixWord, tailWord_83766, baseEnd_83766] using wordTrace_append hprefix tailTrace_83766
  have hstable : (prefixWord ++ tailWord_83766).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83766).length < 2 ^ (prefixWord ++ tailWord_83766).sum := by decide
  have hdescent : baseEnd_83766 < baseStart_83766 := by decide
  rcases family_descends (prefixWord ++ tailWord_83766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83794 : List Nat := [3, 2, 2, 1, 1, 3, 3, 2, 3]
def baseStart_83794 : Nat := 118140960795 + 83794 * 2 ^ 59
def prefixEnd_83794 : Nat := 4983230072969 + 3 ^ 40 * 83794 * 2
def baseEnd_83794 : Nat := 38245864855955901590795

theorem tailTrace_83794 : CollatzResearch.WordTrace tailWord_83794 prefixEnd_83794 38245864855955901590795 := by
  unfold tailWord_83794
  simp only [CollatzResearch.WordTrace]
  refine ⟨764054564609030930240609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2037478838957415813974957 764054564609030930240609)
  ·
    refine ⟨573040923456773197680457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 764054564609030930240609 573040923456773197680457)
    ·
      refine ⟨429780692592579898260343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 573040923456773197680457 429780692592579898260343)
      ·
        refine ⟨644671038888869847390515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 429780692592579898260343 644671038888869847390515)
        ·
          refine ⟨967006558333304771085773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 644671038888869847390515 967006558333304771085773)
          ·
            refine ⟨362627459374989289157165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 967006558333304771085773 362627459374989289157165)
            ·
              refine ⟨135985297265620983433937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 362627459374989289157165 135985297265620983433937)
              ·
                refine ⟨101988972949215737575453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 135985297265620983433937 101988972949215737575453)
                ·
                  refine ⟨38245864855955901590795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 101988972949215737575453 38245864855955901590795)
                  ·
                    rfl

theorem cell20_83794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 3, 2, 3].length) (baseStart_83794 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83794 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83794 prefixEnd_83794 := by exact prefixLift 83794
  have htrace : WordTrace (prefixWord ++ tailWord_83794) baseStart_83794 baseEnd_83794 := by
    simpa [prefixWord, tailWord_83794, baseEnd_83794] using wordTrace_append hprefix tailTrace_83794
  have hstable : (prefixWord ++ tailWord_83794).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83794).length < 2 ^ (prefixWord ++ tailWord_83794).sum := by decide
  have hdescent : baseEnd_83794 < baseStart_83794 := by decide
  rcases family_descends (prefixWord ++ tailWord_83794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83801 : List Nat := [1, 2, 1, 2, 2, 3, 1, 6, 2]
def baseStart_83801 : Nat := 118140960795 + 83801 * 2 ^ 59
def prefixEnd_83801 : Nat := 4983230072969 + 3 ^ 40 * 83801 * 2
def baseEnd_83801 : Nat := 38249059846694988357433

theorem tailTrace_83801 : CollatzResearch.WordTrace tailWord_83801 prefixEnd_83801 38249059846694988357433 := by
  unfold tailWord_83801
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056473569410763916467257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2037649046273842610978171 3056473569410763916467257)
  ·
    refine ⟨2292355177058072937350443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3056473569410763916467257 2292355177058072937350443)
    ·
      refine ⟨3438532765587109406025665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2292355177058072937350443 3438532765587109406025665)
      ·
        refine ⟨2578899574190332054519249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3438532765587109406025665 2578899574190332054519249)
        ·
          refine ⟨1934174680642749040889437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2578899574190332054519249 1934174680642749040889437)
          ·
            refine ⟨725315505241030890333539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1934174680642749040889437 725315505241030890333539)
            ·
              refine ⟨1087973257861546335500309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 725315505241030890333539 1087973257861546335500309)
              ·
                refine ⟨50998746462259984476577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1087973257861546335500309 50998746462259984476577)
                ·
                  refine ⟨38249059846694988357433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 50998746462259984476577 38249059846694988357433)
                  ·
                    rfl

theorem cell20_83801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 6, 2].length) (baseStart_83801 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83801 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83801 prefixEnd_83801 := by exact prefixLift 83801
  have htrace : WordTrace (prefixWord ++ tailWord_83801) baseStart_83801 baseEnd_83801 := by
    simpa [prefixWord, tailWord_83801, baseEnd_83801] using wordTrace_append hprefix tailTrace_83801
  have hstable : (prefixWord ++ tailWord_83801).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83801).length < 2 ^ (prefixWord ++ tailWord_83801).sum := by decide
  have hdescent : baseEnd_83801 < baseStart_83801 := by decide
  rcases family_descends (prefixWord ++ tailWord_83801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83811 : List Nat := [1, 1, 1, 5, 4, 1, 3, 1, 3]
def baseStart_83811 : Nat := 118140960795 + 83811 * 2 ^ 59
def prefixEnd_83811 : Nat := 4983230072969 + 3 ^ 40 * 83811 * 2
def baseEnd_83811 : Nat := 38253624119179398024059

theorem tailTrace_83811 : CollatzResearch.WordTrace tailWord_83811 prefixEnd_83811 38253624119179398024059 := by
  unfold tailWord_83811
  simp only [CollatzResearch.WordTrace]
  refine ⟨3056838299374535624331287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2037892199583023749554191 3056838299374535624331287)
  ·
    refine ⟨4585257449061803436496931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3056838299374535624331287 4585257449061803436496931)
    ·
      refine ⟨6877886173592705154745397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4585257449061803436496931 6877886173592705154745397)
      ·
        refine ⟨644801828774316108257381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 6877886173592705154745397 644801828774316108257381)
        ·
          refine ⟨120900342895184270298259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 644801828774316108257381 120900342895184270298259)
          ·
            refine ⟨181350514342776405447389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 120900342895184270298259 181350514342776405447389)
            ·
              refine ⟨68006442878541152042771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181350514342776405447389 68006442878541152042771)
              ·
                refine ⟨102009664317811728064157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68006442878541152042771 102009664317811728064157)
                ·
                  refine ⟨38253624119179398024059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102009664317811728064157 38253624119179398024059)
                  ·
                    rfl

theorem cell20_83811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 3, 1, 3].length) (baseStart_83811 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83811 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83811 prefixEnd_83811 := by exact prefixLift 83811
  have htrace : WordTrace (prefixWord ++ tailWord_83811) baseStart_83811 baseEnd_83811 := by
    simpa [prefixWord, tailWord_83811, baseEnd_83811] using wordTrace_append hprefix tailTrace_83811
  have hstable : (prefixWord ++ tailWord_83811).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83811).length < 2 ^ (prefixWord ++ tailWord_83811).sum := by decide
  have hdescent : baseEnd_83811 < baseStart_83811 := by decide
  rcases family_descends (prefixWord ++ tailWord_83811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83862 : List Nat := [5, 3, 1, 1, 2, 2, 2, 1, 3]
def baseStart_83862 : Nat := 118140960795 + 83862 * 2 ^ 59
def prefixEnd_83862 : Nat := 4983230072969 + 3 ^ 40 * 83862 * 2
def baseEnd_83862 : Nat := 38276901908849887323851

theorem tailTrace_83862 : CollatzResearch.WordTrace tailWord_83862 prefixEnd_83862 38276901908849887323851 := by
  unfold tailWord_83862
  simp only [CollatzResearch.WordTrace]
  refine ⟨191168651386860708402365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2039132281459847556291893 191168651386860708402365)
  ·
    refine ⟨71688244270072765650887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 191168651386860708402365 71688244270072765650887)
    ·
      refine ⟨107532366405109148476331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 71688244270072765650887 107532366405109148476331)
      ·
        refine ⟨161298549607663722714497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 107532366405109148476331 161298549607663722714497)
        ·
          refine ⟨120973912205747792035873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 161298549607663722714497 120973912205747792035873)
          ·
            refine ⟨90730434154310844026905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 120973912205747792035873 90730434154310844026905)
            ·
              refine ⟨68047825615733133020179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 90730434154310844026905 68047825615733133020179)
              ·
                refine ⟨102071738423599699530269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68047825615733133020179 102071738423599699530269)
                ·
                  refine ⟨38276901908849887323851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102071738423599699530269 38276901908849887323851)
                  ·
                    rfl

theorem cell20_83862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_83862 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83862 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83862 prefixEnd_83862 := by exact prefixLift 83862
  have htrace : WordTrace (prefixWord ++ tailWord_83862) baseStart_83862 baseEnd_83862 := by
    simpa [prefixWord, tailWord_83862, baseEnd_83862] using wordTrace_append hprefix tailTrace_83862
  have hstable : (prefixWord ++ tailWord_83862).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83862).length < 2 ^ (prefixWord ++ tailWord_83862).sum := by decide
  have hdescent : baseEnd_83862 < baseStart_83862 := by decide
  rcases family_descends (prefixWord ++ tailWord_83862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83915 : List Nat := [1, 1, 1, 1, 3, 4, 3, 4, 2]
def baseStart_83915 : Nat := 118140960795 + 83915 * 2 ^ 59
def prefixEnd_83915 : Nat := 4983230072969 + 3 ^ 40 * 83915 * 2
def baseEnd_83915 : Nat := 38301092553017258556967

theorem tailTrace_83915 : CollatzResearch.WordTrace tailWord_83915 prefixEnd_83915 38301092553017258556967 := by
  unfold tailWord_83915
  simp only [CollatzResearch.WordTrace]
  refine ⟨3060631490997761386117199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2040420993998507590744799 3060631490997761386117199)
  ·
    refine ⟨4590947236496642079175799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3060631490997761386117199 4590947236496642079175799)
    ·
      refine ⟨6886420854744963118763699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4590947236496642079175799 6886420854744963118763699)
      ·
        refine ⟨10329631282117444678145549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6886420854744963118763699 10329631282117444678145549)
        ·
          refine ⟨3873611730794041754304581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10329631282117444678145549 3873611730794041754304581)
          ·
            refine ⟨726302199523882828932109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3873611730794041754304581 726302199523882828932109)
            ·
              refine ⟨272363324821456060849541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 726302199523882828932109 272363324821456060849541)
              ·
                refine ⟨51068123404023011409289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 272363324821456060849541 51068123404023011409289)
                ·
                  refine ⟨38301092553017258556967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51068123404023011409289 38301092553017258556967)
                  ·
                    rfl

theorem cell20_83915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 4, 3, 4, 2].length) (baseStart_83915 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83915 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83915 prefixEnd_83915 := by exact prefixLift 83915
  have htrace : WordTrace (prefixWord ++ tailWord_83915) baseStart_83915 baseEnd_83915 := by
    simpa [prefixWord, tailWord_83915, baseEnd_83915] using wordTrace_append hprefix tailTrace_83915
  have hstable : (prefixWord ++ tailWord_83915).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83915).length < 2 ^ (prefixWord ++ tailWord_83915).sum := by decide
  have hdescent : baseEnd_83915 < baseStart_83915 := by decide
  rcases family_descends (prefixWord ++ tailWord_83915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_83995 : List Nat := [1, 1, 1, 1, 1, 1, 3, 5, 6]
def baseStart_83995 : Nat := 118140960795 + 83995 * 2 ^ 59
def prefixEnd_83995 : Nat := 4983230072969 + 3 ^ 40 * 83995 * 2
def baseEnd_83995 : Nat := 38337606732892535889973

theorem tailTrace_83995 : CollatzResearch.WordTrace tailWord_83995 prefixEnd_83995 38337606732892535889973 := by
  unfold tailWord_83995
  simp only [CollatzResearch.WordTrace]
  refine ⟨3063549330707935049029439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2042366220471956699352959 3063549330707935049029439)
  ·
    refine ⟨4595323996061902573544159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3063549330707935049029439 4595323996061902573544159)
    ·
      refine ⟨6892985994092853860316239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4595323996061902573544159 6892985994092853860316239)
      ·
        refine ⟨10339478991139280790474359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6892985994092853860316239 10339478991139280790474359)
        ·
          refine ⟨15509218486708921185711539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10339478991139280790474359 15509218486708921185711539)
          ·
            refine ⟨23263827730063381778567309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 15509218486708921185711539 23263827730063381778567309)
            ·
              refine ⟨8723935398773768166962741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23263827730063381778567309 8723935398773768166962741)
              ·
                refine ⟨817868943635040765652757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8723935398773768166962741 817868943635040765652757)
                ·
                  refine ⟨38337606732892535889973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 817868943635040765652757 38337606732892535889973)
                  ·
                    rfl

theorem cell20_83995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 5, 6].length) (baseStart_83995 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_83995 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_83995 prefixEnd_83995 := by exact prefixLift 83995
  have htrace : WordTrace (prefixWord ++ tailWord_83995) baseStart_83995 baseEnd_83995 := by
    simpa [prefixWord, tailWord_83995, baseEnd_83995] using wordTrace_append hprefix tailTrace_83995
  have hstable : (prefixWord ++ tailWord_83995).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_83995).length < 2 ^ (prefixWord ++ tailWord_83995).sum := by decide
  have hdescent : baseEnd_83995 < baseStart_83995 := by decide
  rcases family_descends (prefixWord ++ tailWord_83995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84004 : List Nat := [2, 3, 1, 4, 3, 1, 1, 3, 2]
def baseStart_84004 : Nat := 118140960795 + 84004 * 2 ^ 59
def prefixEnd_84004 : Nat := 4983230072969 + 3 ^ 40 * 84004 * 2
def baseEnd_84004 : Nat := 38341714578128504589937

theorem tailTrace_84004 : CollatzResearch.WordTrace tailWord_84004 prefixEnd_84004 38341714578128504589937 := by
  unfold tailWord_84004
  simp only [CollatzResearch.WordTrace]
  refine ⟨1531938793837664793053533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2042585058450219724071377 1531938793837664793053533)
  ·
    refine ⟨574477047689124297395075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1531938793837664793053533 574477047689124297395075)
    ·
      refine ⟨861715571533686446092613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 574477047689124297395075 861715571533686446092613)
      ·
        refine ⟨161571669662566208642365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 861715571533686446092613 161571669662566208642365)
        ·
          refine ⟨60589376123462328240887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 161571669662566208642365 60589376123462328240887)
          ·
            refine ⟨90884064185193492361331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 60589376123462328240887 90884064185193492361331)
            ·
              refine ⟨136326096277790238541997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 90884064185193492361331 136326096277790238541997)
              ·
                refine ⟨51122286104171339453249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136326096277790238541997 51122286104171339453249)
                ·
                  refine ⟨38341714578128504589937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51122286104171339453249 38341714578128504589937)
                  ·
                    rfl

theorem cell20_84004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 3, 2].length) (baseStart_84004 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84004 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84004 prefixEnd_84004 := by exact prefixLift 84004
  have htrace : WordTrace (prefixWord ++ tailWord_84004) baseStart_84004 baseEnd_84004 := by
    simpa [prefixWord, tailWord_84004, baseEnd_84004] using wordTrace_append hprefix tailTrace_84004
  have hstable : (prefixWord ++ tailWord_84004).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84004).length < 2 ^ (prefixWord ++ tailWord_84004).sum := by decide
  have hdescent : baseEnd_84004 < baseStart_84004 := by decide
  rcases family_descends (prefixWord ++ tailWord_84004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84022 : List Nat := [5, 1, 2, 1, 1, 1, 2, 4, 3]
def baseStart_84022 : Nat := 118140960795 + 84022 * 2 ^ 59
def prefixEnd_84022 : Nat := 4983230072969 + 3 ^ 40 * 84022 * 2
def baseEnd_84022 : Nat := 38349930268600441989863

theorem tailTrace_84022 : CollatzResearch.WordTrace tailWord_84022 prefixEnd_84022 38349930268600441989863 := by
  unfold tailWord_84022
  simp only [CollatzResearch.WordTrace]
  refine ⟨191533381350632416266395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 2043022734406745773508213 191533381350632416266395)
  ·
    refine ⟨287300072025948624399593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 191533381350632416266395 287300072025948624399593)
    ·
      refine ⟨215475054019461468299695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 287300072025948624399593 215475054019461468299695)
      ·
        refine ⟨323212581029192202449543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215475054019461468299695 323212581029192202449543)
        ·
          refine ⟨484818871543788303674315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 323212581029192202449543 484818871543788303674315)
          ·
            refine ⟨727228307315682455511473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 484818871543788303674315 727228307315682455511473)
            ·
              refine ⟨545421230486761841633605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 727228307315682455511473 545421230486761841633605)
              ·
                refine ⟨102266480716267845306301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 545421230486761841633605 102266480716267845306301)
                ·
                  refine ⟨38349930268600441989863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102266480716267845306301 38349930268600441989863)
                  ·
                    rfl

theorem cell20_84022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_84022 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84022 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84022 prefixEnd_84022 := by exact prefixLift 84022
  have htrace : WordTrace (prefixWord ++ tailWord_84022) baseStart_84022 baseEnd_84022 := by
    simpa [prefixWord, tailWord_84022, baseEnd_84022] using wordTrace_append hprefix tailTrace_84022
  have hstable : (prefixWord ++ tailWord_84022).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84022).length < 2 ^ (prefixWord ++ tailWord_84022).sum := by decide
  have hdescent : baseEnd_84022 < baseStart_84022 := by decide
  rcases family_descends (prefixWord ++ tailWord_84022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84025 : List Nat := [1, 2, 1, 5, 3, 1, 3, 2, 2]
def baseStart_84025 : Nat := 118140960795 + 84025 * 2 ^ 59
def prefixEnd_84025 : Nat := 4983230072969 + 3 ^ 40 * 84025 * 2
def baseEnd_84025 : Nat := 38351299550345764889851

theorem tailTrace_84025 : CollatzResearch.WordTrace tailWord_84025 prefixEnd_84025 38351299550345764889851 := by
  unfold tailWord_84025
  simp only [CollatzResearch.WordTrace]
  refine ⟨3064643520599250172621529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2043095680399500115081019 3064643520599250172621529)
  ·
    refine ⟨2298482640449437629466147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3064643520599250172621529 2298482640449437629466147)
    ·
      refine ⟨3447723960674156444199221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2298482640449437629466147 3447723960674156444199221)
      ·
        refine ⟨323224121313202166643677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3447723960674156444199221 323224121313202166643677)
        ·
          refine ⟨121209045492450812491379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 323224121313202166643677 121209045492450812491379)
          ·
            refine ⟨181813568238676218737069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121209045492450812491379 181813568238676218737069)
            ·
              refine ⟨68180088089503582026401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 181813568238676218737069 68180088089503582026401)
              ·
                refine ⟨51135066067127686519801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68180088089503582026401 51135066067127686519801)
                ·
                  refine ⟨38351299550345764889851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51135066067127686519801 38351299550345764889851)
                  ·
                    rfl

theorem cell20_84025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 2, 2].length) (baseStart_84025 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84025 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84025 prefixEnd_84025 := by exact prefixLift 84025
  have htrace : WordTrace (prefixWord ++ tailWord_84025) baseStart_84025 baseEnd_84025 := by
    simpa [prefixWord, tailWord_84025, baseEnd_84025] using wordTrace_append hprefix tailTrace_84025
  have hstable : (prefixWord ++ tailWord_84025).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84025).length < 2 ^ (prefixWord ++ tailWord_84025).sum := by decide
  have hdescent : baseEnd_84025 < baseStart_84025 := by decide
  rcases family_descends (prefixWord ++ tailWord_84025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84074 : List Nat := [3, 1, 3, 2, 4, 7]
def baseStart_84074 : Nat := 118140960795 + 84074 * 2 ^ 59
def prefixEnd_84074 : Nat := 4983230072969 + 3 ^ 40 * 84074 * 2
def baseEnd_84074 : Nat := 1421246832797013787271

theorem tailTrace_84074 : CollatzResearch.WordTrace tailWord_84074 prefixEnd_84074 1421246832797013787271 := by
  unfold tailWord_84074
  simp only [CollatzResearch.WordTrace]
  refine ⟨766607674355432885288819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2044287131614487694103517 766607674355432885288819)
  ·
    refine ⟨1149911511533149327933229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 766607674355432885288819 1149911511533149327933229)
    ·
      refine ⟨431216816824930997974961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1149911511533149327933229 431216816824930997974961)
      ·
        refine ⟨323412612618698248481221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 431216816824930997974961 323412612618698248481221)
        ·
          refine ⟨60639864866005921590229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 323412612618698248481221 60639864866005921590229)
          ·
            refine ⟨1421246832797013787271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 60639864866005921590229 1421246832797013787271)
            ·
              rfl

theorem cell20_84074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 4, 7].length) (baseStart_84074 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84074 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84074 prefixEnd_84074 := by exact prefixLift 84074
  have htrace : WordTrace (prefixWord ++ tailWord_84074) baseStart_84074 baseEnd_84074 := by
    simpa [prefixWord, tailWord_84074, baseEnd_84074] using wordTrace_append hprefix tailTrace_84074
  have hstable : (prefixWord ++ tailWord_84074).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84074).length < 2 ^ (prefixWord ++ tailWord_84074).sum := by decide
  have hdescent : baseEnd_84074 < baseStart_84074 := by decide
  rcases family_descends (prefixWord ++ tailWord_84074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84081 : List Nat := [1, 2, 2, 2, 1, 1, 6, 2, 3]
def baseStart_84081 : Nat := 118140960795 + 84081 * 2 ^ 59
def prefixEnd_84081 : Nat := 4983230072969 + 3 ^ 40 * 84081 * 2
def baseEnd_84081 : Nat := 38376859476258459022955

theorem tailTrace_84081 : CollatzResearch.WordTrace tailWord_84081 prefixEnd_84081 38376859476258459022955 := by
  unfold tailWord_84081
  simp only [CollatzResearch.WordTrace]
  refine ⟨3066686008396371736660097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2044457338930914491106731 3066686008396371736660097)
  ·
    refine ⟨2300014506297278802495073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3066686008396371736660097 2300014506297278802495073)
    ·
      refine ⟨1725010879722959101871305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2300014506297278802495073 1725010879722959101871305)
      ·
        refine ⟨1293758159792219326403479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1725010879722959101871305 1293758159792219326403479)
        ·
          refine ⟨1940637239688328989605219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1293758159792219326403479 1940637239688328989605219)
          ·
            refine ⟨2910955859532493484407829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1940637239688328989605219 2910955859532493484407829)
            ·
              refine ⟨136451055915585632081617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 2910955859532493484407829 136451055915585632081617)
              ·
                refine ⟨102338291936689224061213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136451055915585632081617 102338291936689224061213)
                ·
                  refine ⟨38376859476258459022955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102338291936689224061213 38376859476258459022955)
                  ·
                    rfl

theorem cell20_84081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 6, 2, 3].length) (baseStart_84081 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84081 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84081 prefixEnd_84081 := by exact prefixLift 84081
  have htrace : WordTrace (prefixWord ++ tailWord_84081) baseStart_84081 baseEnd_84081 := by
    simpa [prefixWord, tailWord_84081, baseEnd_84081] using wordTrace_append hprefix tailTrace_84081
  have hstable : (prefixWord ++ tailWord_84081).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84081).length < 2 ^ (prefixWord ++ tailWord_84081).sum := by decide
  have hdescent : baseEnd_84081 < baseStart_84081 := by decide
  rcases family_descends (prefixWord ++ tailWord_84081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84185 : List Nat := [1, 2, 1, 2, 3, 1, 2, 2, 6]
def baseStart_84185 : Nat := 118140960795 + 84185 * 2 ^ 59
def prefixEnd_84185 : Nat := 4983230072969 + 3 ^ 40 * 84185 * 2
def baseEnd_84185 : Nat := 38424327910096319555863

theorem tailTrace_84185 : CollatzResearch.WordTrace tailWord_84185 prefixEnd_84185 38424327910096319555863 := by
  unfold tailWord_84185
  simp only [CollatzResearch.WordTrace]
  refine ⟨3070479200019597498446009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2046986133346398332297339 3070479200019597498446009)
  ·
    refine ⟨2302859400014698123834507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3070479200019597498446009 2302859400014698123834507)
    ·
      refine ⟨3454289100022047185751761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2302859400014698123834507 3454289100022047185751761)
      ·
        refine ⟨2590716825016535389313821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3454289100022047185751761 2590716825016535389313821)
        ·
          refine ⟨971518809381200770992683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2590716825016535389313821 971518809381200770992683)
          ·
            refine ⟨1457278214071801156489025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 971518809381200770992683 1457278214071801156489025)
            ·
              refine ⟨1092958660553850867366769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1457278214071801156489025 1092958660553850867366769)
              ·
                refine ⟨819718995415388150525077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1092958660553850867366769 819718995415388150525077)
                ·
                  refine ⟨38424327910096319555863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 819718995415388150525077 38424327910096319555863)
                  ·
                    rfl

theorem cell20_84185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_84185 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84185 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84185 prefixEnd_84185 := by exact prefixLift 84185
  have htrace : WordTrace (prefixWord ++ tailWord_84185) baseStart_84185 baseEnd_84185 := by
    simpa [prefixWord, tailWord_84185, baseEnd_84185] using wordTrace_append hprefix tailTrace_84185
  have hstable : (prefixWord ++ tailWord_84185).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84185).length < 2 ^ (prefixWord ++ tailWord_84185).sum := by decide
  have hdescent : baseEnd_84185 < baseStart_84185 := by decide
  rcases family_descends (prefixWord ++ tailWord_84185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84194 : List Nat := [3, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_84194 : Nat := 118140960795 + 84194 * 2 ^ 59
def prefixEnd_84194 : Nat := 4983230072969 + 3 ^ 40 * 84194 * 2
def baseEnd_84194 : Nat := 38428435755332288255827

theorem tailTrace_84194 : CollatzResearch.WordTrace tailWord_84194 prefixEnd_84194 38428435755332288255827 := by
  unfold tailWord_84194
  simp only [CollatzResearch.WordTrace]
  refine ⟨767701864246748008880909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2047204971324661357015757 767701864246748008880909)
  ·
    refine ⟨287888199092530503330341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 767701864246748008880909 287888199092530503330341)
    ·
      refine ⟨53979037329849469374439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 287888199092530503330341 53979037329849469374439)
      ·
        refine ⟨80968555994774204061659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 53979037329849469374439 80968555994774204061659)
        ·
          refine ⟨121452833992161306092489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 80968555994774204061659 121452833992161306092489)
          ·
            refine ⟨91089625494120979569367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121452833992161306092489 91089625494120979569367)
            ·
              refine ⟨136634438241181469354051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 91089625494120979569367 136634438241181469354051)
              ·
                refine ⟨204951657361772204031077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 136634438241181469354051 204951657361772204031077)
                ·
                  refine ⟨38428435755332288255827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 204951657361772204031077 38428435755332288255827)
                  ·
                    rfl

theorem cell20_84194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_84194 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84194 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84194 prefixEnd_84194 := by exact prefixLift 84194
  have htrace : WordTrace (prefixWord ++ tailWord_84194) baseStart_84194 baseEnd_84194 := by
    simpa [prefixWord, tailWord_84194, baseEnd_84194] using wordTrace_append hprefix tailTrace_84194
  have hstable : (prefixWord ++ tailWord_84194).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84194).length < 2 ^ (prefixWord ++ tailWord_84194).sum := by decide
  have hdescent : baseEnd_84194 < baseStart_84194 := by decide
  rcases family_descends (prefixWord ++ tailWord_84194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84223 : List Nat := [1, 1, 2, 2, 1, 4, 2, 1, 6]
def baseStart_84223 : Nat := 118140960795 + 84223 * 2 ^ 59
def prefixEnd_84223 : Nat := 4983230072969 + 3 ^ 40 * 84223 * 2
def baseEnd_84223 : Nat := 38441672145537076289041

theorem tailTrace_84223 : CollatzResearch.WordTrace tailWord_84223 prefixEnd_84223 38441672145537076289041 := by
  unfold tailWord_84223
  simp only [CollatzResearch.WordTrace]
  refine ⟨3071865173881929988329323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2047910115921286658886215 3071865173881929988329323)
  ·
    refine ⟨4607797760822894982493985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3071865173881929988329323 4607797760822894982493985)
    ·
      refine ⟨3455848320617171236870489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4607797760822894982493985 3455848320617171236870489)
      ·
        refine ⟨2591886240462878427652867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3455848320617171236870489 2591886240462878427652867)
        ·
          refine ⟨3887829360694317641479301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2591886240462878427652867 3887829360694317641479301)
          ·
            refine ⟨728968005130184557777369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3887829360694317641479301 728968005130184557777369)
            ·
              refine ⟨546726003847638418333027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 728968005130184557777369 546726003847638418333027)
              ·
                refine ⟨820089005771457627499541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 546726003847638418333027 820089005771457627499541)
                ·
                  refine ⟨38441672145537076289041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 820089005771457627499541 38441672145537076289041)
                  ·
                    rfl

theorem cell20_84223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_84223 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84223 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84223 prefixEnd_84223 := by exact prefixLift 84223
  have htrace : WordTrace (prefixWord ++ tailWord_84223) baseStart_84223 baseEnd_84223 := by
    simpa [prefixWord, tailWord_84223, baseEnd_84223] using wordTrace_append hprefix tailTrace_84223
  have hstable : (prefixWord ++ tailWord_84223).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84223).length < 2 ^ (prefixWord ++ tailWord_84223).sum := by decide
  have hdescent : baseEnd_84223 < baseStart_84223 := by decide
  rcases family_descends (prefixWord ++ tailWord_84223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84226 : List Nat := [3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_84226 : Nat := 118140960795 + 84226 * 2 ^ 59
def prefixEnd_84226 : Nat := 4983230072969 + 3 ^ 40 * 84226 * 2
def baseEnd_84226 : Nat := 12814347142427466396343

theorem tailTrace_84226 : CollatzResearch.WordTrace tailWord_84226 prefixEnd_84226 12814347142427466396343 := by
  unfold tailWord_84226
  simp only [CollatzResearch.WordTrace]
  refine ⟨767993648217765375172133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2047983061914041000459021 767993648217765375172133)
  ·
    refine ⟨143998809040831007844775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 767993648217765375172133 143998809040831007844775)
    ·
      refine ⟨215998213561246511767163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 143998809040831007844775 215998213561246511767163)
      ·
        refine ⟨323997320341869767650745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 215998213561246511767163 323997320341869767650745)
        ·
          refine ⟨242997990256402325738059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 323997320341869767650745 242997990256402325738059)
          ·
            refine ⟨364496985384603488607089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 242997990256402325738059 364496985384603488607089)
            ·
              refine ⟨273372739038452616455317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 364496985384603488607089 273372739038452616455317)
              ·
                refine ⟨12814347142427466396343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 273372739038452616455317 12814347142427466396343)
                ·
                  rfl

theorem cell20_84226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_84226 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84226 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84226 prefixEnd_84226 := by exact prefixLift 84226
  have htrace : WordTrace (prefixWord ++ tailWord_84226) baseStart_84226 baseEnd_84226 := by
    simpa [prefixWord, tailWord_84226, baseEnd_84226] using wordTrace_append hprefix tailTrace_84226
  have hstable : (prefixWord ++ tailWord_84226).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84226).length < 2 ^ (prefixWord ++ tailWord_84226).sum := by decide
  have hdescent : baseEnd_84226 < baseStart_84226 := by decide
  rcases family_descends (prefixWord ++ tailWord_84226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84250 : List Nat := [3, 1, 1, 3, 4, 1, 2, 2, 3]
def baseStart_84250 : Nat := 118140960795 + 84250 * 2 ^ 59
def prefixEnd_84250 : Nat := 4983230072969 + 3 ^ 40 * 84250 * 2
def baseEnd_84250 : Nat := 38453995681244982388931

theorem tailTrace_84250 : CollatzResearch.WordTrace tailWord_84250 prefixEnd_84250 38453995681244982388931 := by
  unfold tailWord_84250
  simp only [CollatzResearch.WordTrace]
  refine ⟨768212486196028399890551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2048566629856075733041469 768212486196028399890551)
  ·
    refine ⟨1152318729294042599835827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 768212486196028399890551 1152318729294042599835827)
    ·
      refine ⟨1728478093941063899753741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1152318729294042599835827 1728478093941063899753741)
      ·
        refine ⟨648179285227898962407653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1728478093941063899753741 648179285227898962407653)
        ·
          refine ⟨121533615980231055451435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 648179285227898962407653 121533615980231055451435)
          ·
            refine ⟨182300423970346583177153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121533615980231055451435 182300423970346583177153)
            ·
              refine ⟨136725317977759937382865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182300423970346583177153 136725317977759937382865)
              ·
                refine ⟨102543988483319953037149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 136725317977759937382865 102543988483319953037149)
                ·
                  refine ⟨38453995681244982388931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102543988483319953037149 38453995681244982388931)
                  ·
                    rfl

theorem cell20_84250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 2, 2, 3].length) (baseStart_84250 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84250 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84250 prefixEnd_84250 := by exact prefixLift 84250
  have htrace : WordTrace (prefixWord ++ tailWord_84250) baseStart_84250 baseEnd_84250 := by
    simpa [prefixWord, tailWord_84250, baseEnd_84250] using wordTrace_append hprefix tailTrace_84250
  have hstable : (prefixWord ++ tailWord_84250).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84250).length < 2 ^ (prefixWord ++ tailWord_84250).sum := by decide
  have hdescent : baseEnd_84250 < baseStart_84250 := by decide
  rcases family_descends (prefixWord ++ tailWord_84250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84295 : List Nat := [1, 1, 4, 1, 2, 2, 4, 3, 2]
def baseStart_84295 : Nat := 118140960795 + 84295 * 2 ^ 59
def prefixEnd_84295 : Nat := 4983230072969 + 3 ^ 40 * 84295 * 2
def baseEnd_84295 : Nat := 38474534907424825888747

theorem tailTrace_84295 : CollatzResearch.WordTrace tailWord_84295 prefixEnd_84295 38474534907424825888747 := by
  unfold tailWord_84295
  simp only [CollatzResearch.WordTrace]
  refine ⟨3074491229621086284950339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2049660819747390856633559 3074491229621086284950339)
  ·
    refine ⟨4611736844431629427425509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3074491229621086284950339 4611736844431629427425509)
    ·
      refine ⟨864700658330930517642283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4611736844431629427425509 864700658330930517642283)
      ·
        refine ⟨1297050987496395776463425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 864700658330930517642283 1297050987496395776463425)
        ·
          refine ⟨972788240622296832347569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1297050987496395776463425 972788240622296832347569)
          ·
            refine ⟨729591180466722624260677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 972788240622296832347569 729591180466722624260677)
            ·
              refine ⟨136798346337510492048877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 729591180466722624260677 136798346337510492048877)
              ·
                refine ⟨51299379876566434518329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 136798346337510492048877 51299379876566434518329)
                ·
                  refine ⟨38474534907424825888747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51299379876566434518329 38474534907424825888747)
                  ·
                    rfl

theorem cell20_84295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 3, 2].length) (baseStart_84295 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84295 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84295 prefixEnd_84295 := by exact prefixLift 84295
  have htrace : WordTrace (prefixWord ++ tailWord_84295) baseStart_84295 baseEnd_84295 := by
    simpa [prefixWord, tailWord_84295, baseEnd_84295] using wordTrace_append hprefix tailTrace_84295
  have hstable : (prefixWord ++ tailWord_84295).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84295).length < 2 ^ (prefixWord ++ tailWord_84295).sum := by decide
  have hdescent : baseEnd_84295 < baseStart_84295 := by decide
  rcases family_descends (prefixWord ++ tailWord_84295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84309 : List Nat := [1, 3, 2, 2, 4, 1, 1, 1, 5]
def baseStart_84309 : Nat := 118140960795 + 84309 * 2 ^ 59
def prefixEnd_84309 : Nat := 4983230072969 + 3 ^ 40 * 84309 * 2
def baseEnd_84309 : Nat := 38480924888902999422023

theorem tailTrace_84309 : CollatzResearch.WordTrace tailWord_84309 prefixEnd_84309 38480924888902999422023 := by
  unfold tailWord_84309
  simp only [CollatzResearch.WordTrace]
  refine ⟨3075001851570366675959981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2050001234380244450639987 3075001851570366675959981)
  ·
    refine ⟨1153125694338887503484993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3075001851570366675959981 1153125694338887503484993)
    ·
      refine ⟨864844270754165627613745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1153125694338887503484993 864844270754165627613745)
      ·
        refine ⟨648633203065624220710309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 864844270754165627613745 648633203065624220710309)
        ·
          refine ⟨121618725574804541383183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 648633203065624220710309 121618725574804541383183)
          ·
            refine ⟨182428088362206812074775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121618725574804541383183 182428088362206812074775)
            ·
              refine ⟨273642132543310218112163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 182428088362206812074775 273642132543310218112163)
              ·
                refine ⟨410463198814965327168245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 273642132543310218112163 410463198814965327168245)
                ·
                  refine ⟨38480924888902999422023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 410463198814965327168245 38480924888902999422023)
                  ·
                    rfl

theorem cell20_84309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 4, 1, 1, 1, 5].length) (baseStart_84309 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84309 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84309 prefixEnd_84309 := by exact prefixLift 84309
  have htrace : WordTrace (prefixWord ++ tailWord_84309) baseStart_84309 baseEnd_84309 := by
    simpa [prefixWord, tailWord_84309, baseEnd_84309] using wordTrace_append hprefix tailTrace_84309
  have hstable : (prefixWord ++ tailWord_84309).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84309).length < 2 ^ (prefixWord ++ tailWord_84309).sum := by decide
  have hdescent : baseEnd_84309 < baseStart_84309 := by decide
  rcases family_descends (prefixWord ++ tailWord_84309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84318 : List Nat := [4, 4, 2, 1, 1, 1, 3, 1, 3]
def baseStart_84318 : Nat := 118140960795 + 84318 * 2 ^ 59
def prefixEnd_84318 : Nat := 4983230072969 + 3 ^ 40 * 84318 * 2
def baseEnd_84318 : Nat := 38485032734138968121987

theorem tailTrace_84318 : CollatzResearch.WordTrace tailWord_84318 prefixEnd_84318 38485032734138968121987 := by
  unfold tailWord_84318
  simp only [CollatzResearch.WordTrace]
  refine ⟨384416263567220151629701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 2050220072358507475358405 384416263567220151629701)
  ·
    refine ⟨72078049418853778430569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 384416263567220151629701 72078049418853778430569)
    ·
      refine ⟨54058537064140333822927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 72078049418853778430569 54058537064140333822927)
      ·
        refine ⟨81087805596210500734391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 54058537064140333822927 81087805596210500734391)
        ·
          refine ⟨121631708394315751101587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81087805596210500734391 121631708394315751101587)
          ·
            refine ⟨182447562591473626652381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121631708394315751101587 182447562591473626652381)
            ·
              refine ⟨68417835971802609994643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182447562591473626652381 68417835971802609994643)
              ·
                refine ⟨102626753957703914991965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68417835971802609994643 102626753957703914991965)
                ·
                  refine ⟨38485032734138968121987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102626753957703914991965 38485032734138968121987)
                  ·
                    rfl

theorem cell20_84318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 3, 1, 3].length) (baseStart_84318 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84318 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84318 prefixEnd_84318 := by exact prefixLift 84318
  have htrace : WordTrace (prefixWord ++ tailWord_84318) baseStart_84318 baseEnd_84318 := by
    simpa [prefixWord, tailWord_84318, baseEnd_84318] using wordTrace_append hprefix tailTrace_84318
  have hstable : (prefixWord ++ tailWord_84318).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84318).length < 2 ^ (prefixWord ++ tailWord_84318).sum := by decide
  have hdescent : baseEnd_84318 < baseStart_84318 := by decide
  rcases family_descends (prefixWord ++ tailWord_84318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84361 : List Nat := [1, 2, 1, 1, 6, 3, 6]
def baseStart_84361 : Nat := 118140960795 + 84361 * 2 ^ 59
def prefixEnd_84361 : Nat := 4983230072969 + 3 ^ 40 * 84361 * 2
def baseEnd_84361 : Nat := 4278295456202436632053

theorem tailTrace_84361 : CollatzResearch.WordTrace tailWord_84361 prefixEnd_84361 4278295456202436632053 := by
  unfold tailWord_84361
  simp only [CollatzResearch.WordTrace]
  refine ⟨3076898447381979556852937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2051265631587986371235291 3076898447381979556852937)
  ·
    refine ⟨2307673835536484667639703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3076898447381979556852937 2307673835536484667639703)
    ·
      refine ⟨3461510753304727001459555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2307673835536484667639703 3461510753304727001459555)
      ·
        refine ⟨5192266129957090502189333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3461510753304727001459555 5192266129957090502189333)
        ·
          refine ⟨243387474841738617290125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 5192266129957090502189333 243387474841738617290125)
          ·
            refine ⟨91270303065651981483797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243387474841738617290125 91270303065651981483797)
            ·
              refine ⟨4278295456202436632053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 91270303065651981483797 4278295456202436632053)
              ·
                rfl

theorem cell20_84361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_84361 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84361 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84361 prefixEnd_84361 := by exact prefixLift 84361
  have htrace : WordTrace (prefixWord ++ tailWord_84361) baseStart_84361 baseEnd_84361 := by
    simpa [prefixWord, tailWord_84361, baseEnd_84361] using wordTrace_append hprefix tailTrace_84361
  have hstable : (prefixWord ++ tailWord_84361).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84361).length < 2 ^ (prefixWord ++ tailWord_84361).sum := by decide
  have hdescent : baseEnd_84361 < baseStart_84361 := by decide
  rcases family_descends (prefixWord ++ tailWord_84361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84381 : List Nat := [1, 4, 2, 1, 4, 2, 2, 1, 3]
def baseStart_84381 : Nat := 118140960795 + 84381 * 2 ^ 59
def prefixEnd_84381 : Nat := 4983230072969 + 3 ^ 40 * 84381 * 2
def baseEnd_84381 : Nat := 38513787650790749021729

theorem tailTrace_84381 : CollatzResearch.WordTrace tailWord_84381 prefixEnd_84381 38513787650790749021729 := by
  unfold tailWord_84381
  simp only [CollatzResearch.WordTrace]
  refine ⟨3077627907309522972580997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2051751938206348648387331 3077627907309522972580997)
  ·
    refine ⟨577055232620535557358937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3077627907309522972580997 577055232620535557358937)
    ·
      refine ⟨432791424465401668019203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 577055232620535557358937 432791424465401668019203)
      ·
        refine ⟨649187136698102502028805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 432791424465401668019203 649187136698102502028805)
        ·
          refine ⟨121722588130894219130401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 649187136698102502028805 121722588130894219130401)
          ·
            refine ⟨91291941098170664347801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 121722588130894219130401 91291941098170664347801)
            ·
              refine ⟨68468955823627998260851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91291941098170664347801 68468955823627998260851)
              ·
                refine ⟨102703433735441997391277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68468955823627998260851 102703433735441997391277)
                ·
                  refine ⟨38513787650790749021729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102703433735441997391277 38513787650790749021729)
                  ·
                    rfl

theorem cell20_84381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 2, 2, 1, 3].length) (baseStart_84381 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84381 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84381 prefixEnd_84381 := by exact prefixLift 84381
  have htrace : WordTrace (prefixWord ++ tailWord_84381) baseStart_84381 baseEnd_84381 := by
    simpa [prefixWord, tailWord_84381, baseEnd_84381] using wordTrace_append hprefix tailTrace_84381
  have hstable : (prefixWord ++ tailWord_84381).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84381).length < 2 ^ (prefixWord ++ tailWord_84381).sum := by decide
  have hdescent : baseEnd_84381 < baseStart_84381 := by decide
  rcases family_descends (prefixWord ++ tailWord_84381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84423 : List Nat := [1, 1, 4, 1, 1, 5, 2, 2, 3]
def baseStart_84423 : Nat := 118140960795 + 84423 * 2 ^ 59
def prefixEnd_84423 : Nat := 4983230072969 + 3 ^ 40 * 84423 * 2
def baseEnd_84423 : Nat := 38532957595225269621557

theorem tailTrace_84423 : CollatzResearch.WordTrace tailWord_84423 prefixEnd_84423 38532957595225269621557 := by
  unfold tailWord_84423
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079159773157364145609923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2052773182104909430406615 3079159773157364145609923)
  ·
    refine ⟨4618739659736046218414885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3079159773157364145609923 4618739659736046218414885)
    ·
      refine ⟨866013686200508665952791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4618739659736046218414885 866013686200508665952791)
      ·
        refine ⟨1299020529300762998929187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 866013686200508665952791 1299020529300762998929187)
        ·
          refine ⟨1948530793951144498393781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1299020529300762998929187 1948530793951144498393781)
          ·
            refine ⟨182674761932919796724417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 1948530793951144498393781 182674761932919796724417)
            ·
              refine ⟨137006071449689847543313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182674761932919796724417 137006071449689847543313)
              ·
                refine ⟨102754553587267385657485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 137006071449689847543313 102754553587267385657485)
                ·
                  refine ⟨38532957595225269621557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102754553587267385657485 38532957595225269621557)
                  ·
                    rfl

theorem cell20_84423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 2, 2, 3].length) (baseStart_84423 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84423 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84423 prefixEnd_84423 := by exact prefixLift 84423
  have htrace : WordTrace (prefixWord ++ tailWord_84423) baseStart_84423 baseEnd_84423 := by
    simpa [prefixWord, tailWord_84423, baseEnd_84423] using wordTrace_append hprefix tailTrace_84423
  have hstable : (prefixWord ++ tailWord_84423).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84423).length < 2 ^ (prefixWord ++ tailWord_84423).sum := by decide
  have hdescent : baseEnd_84423 < baseStart_84423 := by decide
  rcases family_descends (prefixWord ++ tailWord_84423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84437 : List Nat := [1, 3, 2, 3, 1, 2, 3, 5]
def baseStart_84437 : Nat := 118140960795 + 84437 * 2 ^ 59
def prefixEnd_84437 : Nat := 4983230072969 + 3 ^ 40 * 84437 * 2
def baseEnd_84437 : Nat := 12846449192234481051611

theorem tailTrace_84437 : CollatzResearch.WordTrace tailWord_84437 prefixEnd_84437 12846449192234481051611 := by
  unfold tailWord_84437
  simp only [CollatzResearch.WordTrace]
  refine ⟨3079670395106644536619565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2053113596737763024413043 3079670395106644536619565)
  ·
    refine ⟨1154876398164991701232337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3079670395106644536619565 1154876398164991701232337)
    ·
      refine ⟨866157298623743775924253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1154876398164991701232337 866157298623743775924253)
      ·
        refine ⟨324808986983903915971595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 866157298623743775924253 324808986983903915971595)
        ·
          refine ⟨487213480475855873957393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 324808986983903915971595 487213480475855873957393)
          ·
            refine ⟨365410110356891905468045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 487213480475855873957393 365410110356891905468045)
            ·
              refine ⟨137028791383834464550517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 365410110356891905468045 137028791383834464550517)
              ·
                refine ⟨12846449192234481051611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137028791383834464550517 12846449192234481051611)
                ·
                  rfl

theorem cell20_84437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 3, 5].length) (baseStart_84437 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84437 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84437 prefixEnd_84437 := by exact prefixLift 84437
  have htrace : WordTrace (prefixWord ++ tailWord_84437) baseStart_84437 baseEnd_84437 := by
    simpa [prefixWord, tailWord_84437, baseEnd_84437] using wordTrace_append hprefix tailTrace_84437
  have hstable : (prefixWord ++ tailWord_84437).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84437).length < 2 ^ (prefixWord ++ tailWord_84437).sum := by decide
  have hdescent : baseEnd_84437 < baseStart_84437 := by decide
  rcases family_descends (prefixWord ++ tailWord_84437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84450 : List Nat := [3, 3, 3, 2, 1, 1, 3, 4]
def baseStart_84450 : Nat := 118140960795 + 84450 * 2 ^ 59
def prefixEnd_84450 : Nat := 4983230072969 + 3 ^ 40 * 84450 * 2
def baseEnd_84450 : Nat := 12848427043644391907149

theorem tailTrace_84450 : CollatzResearch.WordTrace tailWord_84450 prefixEnd_84450 12848427043644391907149 := by
  unfold tailWord_84450
  simp only [CollatzResearch.WordTrace]
  refine ⟨770036136014886939210701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2053429696039698504561869 770036136014886939210701)
  ·
    refine ⟨288763551005582602204013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 770036136014886939210701 288763551005582602204013)
    ·
      refine ⟨108286331627093475826505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 288763551005582602204013 108286331627093475826505)
      ·
        refine ⟨81214748720320106869879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 108286331627093475826505 81214748720320106869879)
        ·
          refine ⟨121822123080480160304819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 81214748720320106869879 121822123080480160304819)
          ·
            refine ⟨182733184620720240457229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 121822123080480160304819 182733184620720240457229)
            ·
              refine ⟨68524944232770090171461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182733184620720240457229 68524944232770090171461)
              ·
                refine ⟨12848427043644391907149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 68524944232770090171461 12848427043644391907149)
                ·
                  rfl

theorem cell20_84450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 1, 3, 4].length) (baseStart_84450 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84450 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84450 prefixEnd_84450 := by exact prefixLift 84450
  have htrace : WordTrace (prefixWord ++ tailWord_84450) baseStart_84450 baseEnd_84450 := by
    simpa [prefixWord, tailWord_84450, baseEnd_84450] using wordTrace_append hprefix tailTrace_84450
  have hstable : (prefixWord ++ tailWord_84450).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84450).length < 2 ^ (prefixWord ++ tailWord_84450).sum := by decide
  have hdescent : baseEnd_84450 < baseStart_84450 := by decide
  rcases family_descends (prefixWord ++ tailWord_84450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84499 : List Nat := [1, 1, 1, 2, 1, 5, 5, 1, 3]
def baseStart_84499 : Nat := 118140960795 + 84499 * 2 ^ 59
def prefixEnd_84499 : Nat := 4983230072969 + 3 ^ 40 * 84499 * 2
def baseEnd_84499 : Nat := 38567646066106783087913

theorem tailTrace_84499 : CollatzResearch.WordTrace tailWord_84499 prefixEnd_84499 38567646066106783087913 := by
  unfold tailWord_84499
  simp only [CollatzResearch.WordTrace]
  refine ⟨3081931720882029125376551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2054621147254686083584367 3081931720882029125376551)
  ·
    refine ⟨4622897581323043688064827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3081931720882029125376551 4622897581323043688064827)
    ·
      refine ⟨6934346371984565532097241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4622897581323043688064827 6934346371984565532097241)
      ·
        refine ⟨5200759778988424149072931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6934346371984565532097241 5200759778988424149072931)
        ·
          refine ⟨7801139668482636223609397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5200759778988424149072931 7801139668482636223609397)
          ·
            refine ⟨731356843920247145963381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7801139668482636223609397 731356843920247145963381)
            ·
              refine ⟨68564704117523169934067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 731356843920247145963381 68564704117523169934067)
              ·
                refine ⟨102847056176284754901101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68564704117523169934067 102847056176284754901101)
                ·
                  refine ⟨38567646066106783087913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102847056176284754901101 38567646066106783087913)
                  ·
                    rfl

theorem cell20_84499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 5, 1, 3].length) (baseStart_84499 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84499 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84499 prefixEnd_84499 := by exact prefixLift 84499
  have htrace : WordTrace (prefixWord ++ tailWord_84499) baseStart_84499 baseEnd_84499 := by
    simpa [prefixWord, tailWord_84499, baseEnd_84499] using wordTrace_append hprefix tailTrace_84499
  have hstable : (prefixWord ++ tailWord_84499).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84499).length < 2 ^ (prefixWord ++ tailWord_84499).sum := by decide
  have hdescent : baseEnd_84499 < baseStart_84499 := by decide
  rcases family_descends (prefixWord ++ tailWord_84499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84540 : List Nat := [2, 2, 2, 2, 3, 2, 3, 2, 2]
def baseStart_84540 : Nat := 118140960795 + 84540 * 2 ^ 59
def prefixEnd_84540 : Nat := 4983230072969 + 3 ^ 40 * 84540 * 2
def baseEnd_84540 : Nat := 38586359583292862721079

theorem tailTrace_84540 : CollatzResearch.WordTrace tailWord_84540 prefixEnd_84540 38586359583292862721079 := by
  unfold tailWord_84540
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541713556866746563809537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2055618075822328751746049 1541713556866746563809537)
  ·
    refine ⟨1156285167650059922857153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1541713556866746563809537 1156285167650059922857153)
    ·
      refine ⟨867213875737544942142865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156285167650059922857153 867213875737544942142865)
      ·
        refine ⟨650410406803158706607149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 867213875737544942142865 650410406803158706607149)
        ·
          refine ⟨243903902551184514977681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 650410406803158706607149 243903902551184514977681)
          ·
            refine ⟨182927926913388386233261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243903902551184514977681 182927926913388386233261)
            ·
              refine ⟨68597972592520644837473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 182927926913388386233261 68597972592520644837473)
              ·
                refine ⟨51448479444390483628105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 68597972592520644837473 51448479444390483628105)
                ·
                  refine ⟨38586359583292862721079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51448479444390483628105 38586359583292862721079)
                  ·
                    rfl

theorem cell20_84540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 2, 3, 2, 2].length) (baseStart_84540 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84540 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84540 prefixEnd_84540 := by exact prefixLift 84540
  have htrace : WordTrace (prefixWord ++ tailWord_84540) baseStart_84540 baseEnd_84540 := by
    simpa [prefixWord, tailWord_84540, baseEnd_84540] using wordTrace_append hprefix tailTrace_84540
  have hstable : (prefixWord ++ tailWord_84540).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84540).length < 2 ^ (prefixWord ++ tailWord_84540).sum := by decide
  have hdescent : baseEnd_84540 < baseStart_84540 := by decide
  rcases family_descends (prefixWord ++ tailWord_84540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84544 : List Nat := [2, 1, 1, 2, 2, 2, 2, 6, 2]
def baseStart_84544 : Nat := 118140960795 + 84544 * 2 ^ 59
def prefixEnd_84544 : Nat := 4983230072969 + 3 ^ 40 * 84544 * 2
def baseEnd_84544 : Nat := 38588185292286626587729

theorem tailTrace_84544 : CollatzResearch.WordTrace tailWord_84544 prefixEnd_84544 38588185292286626587729 := by
  unfold tailWord_84544
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541786502859500905382343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 2055715337146001207176457 1541786502859500905382343)
  ·
    refine ⟨2312679754289251358073515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1541786502859500905382343 2312679754289251358073515)
    ·
      refine ⟨3469019631433877037110273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2312679754289251358073515 3469019631433877037110273)
      ·
        refine ⟨2601764723575407777832705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3469019631433877037110273 2601764723575407777832705)
        ·
          refine ⟨1951323542681555833374529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2601764723575407777832705 1951323542681555833374529)
          ·
            refine ⟨1463492657011166875030897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1951323542681555833374529 1463492657011166875030897)
            ·
              refine ⟨1097619492758375156273173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1463492657011166875030897 1097619492758375156273173)
              ·
                refine ⟨51450913723048835450305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1097619492758375156273173 51450913723048835450305)
                ·
                  refine ⟨38588185292286626587729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 51450913723048835450305 38588185292286626587729)
                  ·
                    rfl

theorem cell20_84544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 6, 2].length) (baseStart_84544 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84544 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84544 prefixEnd_84544 := by exact prefixLift 84544
  have htrace : WordTrace (prefixWord ++ tailWord_84544) baseStart_84544 baseEnd_84544 := by
    simpa [prefixWord, tailWord_84544, baseEnd_84544] using wordTrace_append hprefix tailTrace_84544
  have hstable : (prefixWord ++ tailWord_84544).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84544).length < 2 ^ (prefixWord ++ tailWord_84544).sum := by decide
  have hdescent : baseEnd_84544 < baseStart_84544 := by decide
  rcases family_descends (prefixWord ++ tailWord_84544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84550 : List Nat := [6, 1, 1, 1, 2, 3, 2, 1, 3]
def baseStart_84550 : Nat := 118140960795 + 84550 * 2 ^ 59
def prefixEnd_84550 : Nat := 4983230072969 + 3 ^ 40 * 84550 * 2
def baseEnd_84550 : Nat := 38590923855777272387705

theorem tailTrace_84550 : CollatzResearch.WordTrace tailWord_84550 prefixEnd_84550 38590923855777272387705 := by
  unfold tailWord_84550
  simp only [CollatzResearch.WordTrace]
  refine ⟨96368495115539526108847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 2055861229131509890322069 96368495115539526108847)
  ·
    refine ⟨144552742673309289163271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 96368495115539526108847 144552742673309289163271)
    ·
      refine ⟨216829114009963933744907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 144552742673309289163271 216829114009963933744907)
      ·
        refine ⟨325243671014945900617361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 216829114009963933744907 325243671014945900617361)
        ·
          refine ⟨243932753261209425463021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 325243671014945900617361 243932753261209425463021)
          ·
            refine ⟨91474782472953534548633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 243932753261209425463021 91474782472953534548633)
            ·
              refine ⟨68606086854715150911475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91474782472953534548633 68606086854715150911475)
              ·
                refine ⟨102909130282072726367213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68606086854715150911475 102909130282072726367213)
                ·
                  refine ⟨38590923855777272387705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102909130282072726367213 38590923855777272387705)
                  ·
                    rfl

theorem cell20_84550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 3, 2, 1, 3].length) (baseStart_84550 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84550 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84550 prefixEnd_84550 := by exact prefixLift 84550
  have htrace : WordTrace (prefixWord ++ tailWord_84550) baseStart_84550 baseEnd_84550 := by
    simpa [prefixWord, tailWord_84550, baseEnd_84550] using wordTrace_append hprefix tailTrace_84550
  have hstable : (prefixWord ++ tailWord_84550).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84550).length < 2 ^ (prefixWord ++ tailWord_84550).sum := by decide
  have hdescent : baseEnd_84550 < baseStart_84550 := by decide
  rcases family_descends (prefixWord ++ tailWord_84550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84551 : List Nat := [1, 1, 4, 1, 4, 2, 2, 5]
def baseStart_84551 : Nat := 118140960795 + 84551 * 2 ^ 59
def prefixEnd_84551 : Nat := 4983230072969 + 3 ^ 40 * 84551 * 2
def baseEnd_84551 : Nat := 12863793427675237784789

theorem tailTrace_84551 : CollatzResearch.WordTrace tailWord_84551 prefixEnd_84551 12863793427675237784789 := by
  unfold tailWord_84551
  simp only [CollatzResearch.WordTrace]
  refine ⟨3083828316693642006269507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 2055885544462428004179671 3083828316693642006269507)
  ·
    refine ⟨4625742475040463009404261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3083828316693642006269507 4625742475040463009404261)
    ·
      refine ⟨867326714070086814263299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4625742475040463009404261 867326714070086814263299)
      ·
        refine ⟨1300990071105130221394949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867326714070086814263299 1300990071105130221394949)
        ·
          refine ⟨243935638332211916511553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1300990071105130221394949 243935638332211916511553)
          ·
            refine ⟨182951728749158937383665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 243935638332211916511553 182951728749158937383665)
            ·
              refine ⟨137213796561869203037749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 182951728749158937383665 137213796561869203037749)
              ·
                refine ⟨12863793427675237784789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 137213796561869203037749 12863793427675237784789)
                ·
                  rfl

theorem cell20_84551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 5].length) (baseStart_84551 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84551 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84551 prefixEnd_84551 := by exact prefixLift 84551
  have htrace : WordTrace (prefixWord ++ tailWord_84551) baseStart_84551 baseEnd_84551 := by
    simpa [prefixWord, tailWord_84551, baseEnd_84551] using wordTrace_append hprefix tailTrace_84551
  have hstable : (prefixWord ++ tailWord_84551).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84551).length < 2 ^ (prefixWord ++ tailWord_84551).sum := by decide
  have hdescent : baseEnd_84551 < baseStart_84551 := by decide
  rcases family_descends (prefixWord ++ tailWord_84551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_84554 : List Nat := [3, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_84554 : Nat := 118140960795 + 84554 * 2 ^ 59
def prefixEnd_84554 : Nat := 4983230072969 + 3 ^ 40 * 84554 * 2
def baseEnd_84554 : Nat := 38592749564771036254355

theorem tailTrace_84554 : CollatzResearch.WordTrace tailWord_84554 prefixEnd_84554 38592749564771036254355 := by
  unfold tailWord_84554
  simp only [CollatzResearch.WordTrace]
  refine ⟨770984433920693379657179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 2055958490455182345752477 770984433920693379657179)
  ·
    refine ⟨1156476650881040069485769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 770984433920693379657179 1156476650881040069485769)
    ·
      refine ⟨867357488160780052114327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1156476650881040069485769 867357488160780052114327)
      ·
        refine ⟨1301036232241170078171491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867357488160780052114327 1301036232241170078171491)
        ·
          refine ⟨1951554348361755117257237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1301036232241170078171491 1951554348361755117257237)
          ·
            refine ⟨91479110079457271121433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 1951554348361755117257237 91479110079457271121433)
            ·
              refine ⟨68609332559592953341075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 91479110079457271121433 68609332559592953341075)
              ·
                refine ⟨102913998839389430011613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 68609332559592953341075 102913998839389430011613)
                ·
                  refine ⟨38592749564771036254355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 102913998839389430011613 38592749564771036254355)
                  ·
                    rfl

theorem cell20_84554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_84554 + u * 2 ^ 79) = endpoint ∧
      endpoint < baseStart_84554 + u * 2 ^ 79 := by
  have hprefix : WordTrace prefixWord baseStart_84554 prefixEnd_84554 := by exact prefixLift 84554
  have htrace : WordTrace (prefixWord ++ tailWord_84554) baseStart_84554 baseEnd_84554 := by
    simpa [prefixWord, tailWord_84554, baseEnd_84554] using wordTrace_append hprefix tailTrace_84554
  have hstable : (prefixWord ++ tailWord_84554).sum < 79 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_84554).length < 2 ^ (prefixWord ++ tailWord_84554).sum := by decide
  have hdescent : baseEnd_84554 < baseStart_84554 := by decide
  rcases family_descends (prefixWord ++ tailWord_84554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan20Incremental
