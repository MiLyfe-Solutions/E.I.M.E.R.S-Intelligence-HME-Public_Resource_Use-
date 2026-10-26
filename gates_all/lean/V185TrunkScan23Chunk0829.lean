import V185TrunkScan23Chunk0828

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4904654 : List Nat := [4, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2]
def baseStart_4904654 : Nat := 118140960795 + 4904654 * 2 ^ 59
def prefixEnd_4904654 : Nat := 4983230072969 + 3 ^ 40 * 4904654 * 2
def baseEnd_4904654 : Nat := 2518444945996958752368913

theorem tailTrace_4904654 : CollatzResearch.WordTrace tailWord_4904654 prefixEnd_4904654 2518444945996958752368913 := by
  unfold tailWord_4904654
  simp only [CollatzResearch.WordTrace]
  refine ⟨22360928446660460132466127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119258285048855787373152677 22360928446660460132466127)
  ·
    refine ⟨33541392669990690198699191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22360928446660460132466127 33541392669990690198699191)
    ·
      refine ⟨50312089004986035298048787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33541392669990690198699191 50312089004986035298048787)
      ·
        refine ⟨75468133507479052947073181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50312089004986035298048787 75468133507479052947073181)
        ·
          refine ⟨28300550065304644855152443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75468133507479052947073181 28300550065304644855152443)
          ·
            refine ⟨42450825097956967282728665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28300550065304644855152443 42450825097956967282728665)
            ·
              refine ⟨31838118823467725462046499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42450825097956967282728665 31838118823467725462046499)
              ·
                refine ⟨47757178235201588193069749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31838118823467725462046499 47757178235201588193069749)
                ·
                  refine ⟨4477235459550148893100289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47757178235201588193069749 4477235459550148893100289)
                  ·
                    refine ⟨3357926594662611669825217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4477235459550148893100289 3357926594662611669825217)
                    ·
                      refine ⟨2518444945996958752368913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357926594662611669825217 2518444945996958752368913)
                      ·
                        rfl

theorem cell23_4904654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2].length) (baseStart_4904654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904654 prefixEnd_4904654 := by exact prefixLift 4904654
  have htrace : WordTrace (prefixWord ++ tailWord_4904654) baseStart_4904654 baseEnd_4904654 := by
    simpa [prefixWord, tailWord_4904654, baseEnd_4904654] using wordTrace_append hprefix tailTrace_4904654
  have hstable : (prefixWord ++ tailWord_4904654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904654).length < 2 ^ (prefixWord ++ tailWord_4904654).sum := by decide
  have hdescent : baseEnd_4904654 < baseStart_4904654 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904657 : List Nat := [1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 3]
def baseStart_4904657 : Nat := 118140960795 + 4904657 * 2 ^ 59
def prefixEnd_4904657 : Nat := 4983230072969 + 3 ^ 40 * 4904657 * 2
def baseEnd_4904657 : Nat := 2518446486438922240631399

theorem tailTrace_4904657 : CollatzResearch.WordTrace tailWord_4904657 prefixEnd_4904657 2518446486438922240631399 := by
  unfold tailWord_4904657
  simp only [CollatzResearch.WordTrace]
  refine ⟨178887536992272812572088225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119258357994848541714725483 178887536992272812572088225)
  ·
    refine ⟨134165652744204609429066169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178887536992272812572088225 134165652744204609429066169)
    ·
      refine ⟨100624239558153457071799627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134165652744204609429066169 100624239558153457071799627)
      ·
        refine ⟨150936359337230185607699441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100624239558153457071799627 150936359337230185607699441)
        ·
          refine ⟨113202269502922639205774581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150936359337230185607699441 113202269502922639205774581)
          ·
            refine ⟨10612712765898997425541367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113202269502922639205774581 10612712765898997425541367)
            ·
              refine ⟨15919069148848496138312051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10612712765898997425541367 15919069148848496138312051)
              ·
                refine ⟨23878603723272744207468077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15919069148848496138312051 23878603723272744207468077)
                ·
                  refine ⟨8954476396227279077800529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23878603723272744207468077 8954476396227279077800529)
                  ·
                    refine ⟨6715857297170459308350397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8954476396227279077800529 6715857297170459308350397)
                    ·
                      refine ⟨2518446486438922240631399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6715857297170459308350397 2518446486438922240631399)
                      ·
                        rfl

theorem cell23_4904657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 1, 3, 2, 3].length) (baseStart_4904657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904657 prefixEnd_4904657 := by exact prefixLift 4904657
  have htrace : WordTrace (prefixWord ++ tailWord_4904657) baseStart_4904657 baseEnd_4904657 := by
    simpa [prefixWord, tailWord_4904657, baseEnd_4904657] using wordTrace_append hprefix tailTrace_4904657
  have hstable : (prefixWord ++ tailWord_4904657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904657).length < 2 ^ (prefixWord ++ tailWord_4904657).sum := by decide
  have hdescent : baseEnd_4904657 < baseStart_4904657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904671 : List Nat := [1, 1, 2, 3, 2, 2, 2, 5, 1, 2, 2]
def baseStart_4904671 : Nat := 118140960795 + 4904671 * 2 ^ 59
def prefixEnd_4904671 : Nat := 4983230072969 + 3 ^ 40 * 4904671 * 2
def baseEnd_4904671 : Nat := 2518453675168085185856335

theorem tailTrace_4904671 : CollatzResearch.WordTrace tailWord_4904671 prefixEnd_4904671 2518453675168085185856335 := by
  unfold tailWord_4904671
  simp only [CollatzResearch.WordTrace]
  refine ⟨178888047614222092963097867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119258698409481395308731911 178888047614222092963097867)
  ·
    refine ⟨268332071421333139444646801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178888047614222092963097867 268332071421333139444646801)
    ·
      refine ⟨201249053565999854583485101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268332071421333139444646801 201249053565999854583485101)
      ·
        refine ⟨75468395087249945468806913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201249053565999854583485101 75468395087249945468806913)
        ·
          refine ⟨56601296315437459101605185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75468395087249945468806913 56601296315437459101605185)
          ·
            refine ⟨42450972236578094326203889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56601296315437459101605185 42450972236578094326203889)
            ·
              refine ⟨31838229177433570744652917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42450972236578094326203889 31838229177433570744652917)
              ·
                refine ⟨2984833985384397257311211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31838229177433570744652917 2984833985384397257311211)
                ·
                  refine ⟨4477250978076595885966817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2984833985384397257311211 4477250978076595885966817)
                  ·
                    refine ⟨3357938233557446914475113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4477250978076595885966817 3357938233557446914475113)
                    ·
                      refine ⟨2518453675168085185856335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357938233557446914475113 2518453675168085185856335)
                      ·
                        rfl

theorem cell23_4904671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_4904671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904671 prefixEnd_4904671 := by exact prefixLift 4904671
  have htrace : WordTrace (prefixWord ++ tailWord_4904671) baseStart_4904671 baseEnd_4904671 := by
    simpa [prefixWord, tailWord_4904671, baseEnd_4904671] using wordTrace_append hprefix tailTrace_4904671
  have hstable : (prefixWord ++ tailWord_4904671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904671).length < 2 ^ (prefixWord ++ tailWord_4904671).sum := by decide
  have hdescent : baseEnd_4904671 < baseStart_4904671 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904690 : List Nat := [3, 2, 1, 3, 1, 1, 1, 1, 1, 9]
def baseStart_4904690 : Nat := 118140960795 + 4904690 * 2 ^ 59
def prefixEnd_4904690 : Nat := 4983230072969 + 3 ^ 40 * 4904690 * 2
def baseEnd_4904690 : Nat := 839487810433506870506249

theorem tailTrace_4904690 : CollatzResearch.WordTrace tailWord_4904690 prefixEnd_4904690 839487810433506870506249 := by
  unfold tailWord_4904690
  simp only [CollatzResearch.WordTrace]
  refine ⟨44722185150288314802009881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119259160400768839472026349 44722185150288314802009881)
  ·
    refine ⟨33541638862716236101507411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44722185150288314802009881 33541638862716236101507411)
    ·
      refine ⟨50312458294074354152261117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33541638862716236101507411 50312458294074354152261117)
      ·
        refine ⟨18867171860277882807097919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50312458294074354152261117 18867171860277882807097919)
        ·
          refine ⟨28300757790416824210646879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18867171860277882807097919 28300757790416824210646879)
          ·
            refine ⟨42451136685625236315970319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28300757790416824210646879 42451136685625236315970319)
            ·
              refine ⟨63676705028437854473955479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42451136685625236315970319 63676705028437854473955479)
              ·
                refine ⟨95515057542656781710933219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63676705028437854473955479 95515057542656781710933219)
                ·
                  refine ⟨143272586313985172566399829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95515057542656781710933219 143272586313985172566399829)
                  ·
                    refine ⟨839487810433506870506249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 143272586313985172566399829 839487810433506870506249)
                    ·
                      rfl

theorem cell23_4904690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 1, 1, 1, 9].length) (baseStart_4904690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904690 prefixEnd_4904690 := by exact prefixLift 4904690
  have htrace : WordTrace (prefixWord ++ tailWord_4904690) baseStart_4904690 baseEnd_4904690 := by
    simpa [prefixWord, tailWord_4904690, baseEnd_4904690] using wordTrace_append hprefix tailTrace_4904690
  have hstable : (prefixWord ++ tailWord_4904690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904690).length < 2 ^ (prefixWord ++ tailWord_4904690).sum := by decide
  have hdescent : baseEnd_4904690 < baseStart_4904690 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904714 : List Nat := [3, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2]
def baseStart_4904714 : Nat := 118140960795 + 4904714 * 2 ^ 59
def prefixEnd_4904714 : Nat := 4983230072969 + 3 ^ 40 * 4904714 * 2
def baseEnd_4904714 : Nat := 2518475754836228517618637

theorem tailTrace_4904714 : CollatzResearch.WordTrace tailWord_4904714 prefixEnd_4904714 2518475754836228517618637 := by
  unfold tailWord_4904714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44722403988266577826728299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119259743968710874204608797 44722403988266577826728299)
  ·
    refine ⟨67083605982399866740092449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44722403988266577826728299 67083605982399866740092449)
    ·
      refine ⟨50312704486799900055069337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67083605982399866740092449 50312704486799900055069337)
      ·
        refine ⟨37734528365099925041302003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50312704486799900055069337 37734528365099925041302003)
        ·
          refine ⟨56601792547649887561953005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37734528365099925041302003 56601792547649887561953005)
          ·
            refine ⟨21225672205368707835732377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56601792547649887561953005 21225672205368707835732377)
            ·
              refine ⟨15919254154026530876799283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21225672205368707835732377 15919254154026530876799283)
              ·
                refine ⟨23878881231039796315198925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15919254154026530876799283 23878881231039796315198925)
                ·
                  refine ⟨8954580461639923618199597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23878881231039796315198925 8954580461639923618199597)
                  ·
                    refine ⟨3357967673114971356824849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8954580461639923618199597 3357967673114971356824849)
                    ·
                      refine ⟨2518475754836228517618637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3357967673114971356824849 2518475754836228517618637)
                      ·
                        rfl

theorem cell23_4904714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 2, 1, 3, 3, 2].length) (baseStart_4904714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904714 prefixEnd_4904714 := by exact prefixLift 4904714
  have htrace : WordTrace (prefixWord ++ tailWord_4904714) baseStart_4904714 baseEnd_4904714 := by
    simpa [prefixWord, tailWord_4904714, baseEnd_4904714] using wordTrace_append hprefix tailTrace_4904714
  have hstable : (prefixWord ++ tailWord_4904714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904714).length < 2 ^ (prefixWord ++ tailWord_4904714).sum := by decide
  have hdescent : baseEnd_4904714 < baseStart_4904714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904787 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 3, 7, 2]
def baseStart_4904787 : Nat := 118140960795 + 4904787 * 2 ^ 59
def prefixEnd_4904787 : Nat := 4983230072969 + 3 ^ 40 * 4904787 * 2
def baseEnd_4904787 : Nat := 2518513238924006732005801

theorem tailTrace_4904787 : CollatzResearch.WordTrace tailWord_4904787 prefixEnd_4904787 2518513238924006732005801 := by
  unfold tailWord_4904787
  simp only [CollatzResearch.WordTrace]
  refine ⟨178892278481801844774320615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119261518987867896516213743 178892278481801844774320615)
  ·
    refine ⟨268338417722702767161480923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178892278481801844774320615 268338417722702767161480923)
    ·
      refine ⟨402507626584054150742221385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268338417722702767161480923 402507626584054150742221385)
      ·
        refine ⟨301880719938040613056666039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402507626584054150742221385 301880719938040613056666039)
        ·
          refine ⟨452821079907060919584999059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301880719938040613056666039 452821079907060919584999059)
          ·
            refine ⟨679231619860591379377498589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452821079907060919584999059 679231619860591379377498589)
            ·
              refine ⟨254711857447721767266561971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 679231619860591379377498589 254711857447721767266561971)
              ·
                refine ⟨382067786171582650899842957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254711857447721767266561971 382067786171582650899842957)
                ·
                  refine ⟨143275419814343494087441109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382067786171582650899842957 143275419814343494087441109)
                  ·
                    refine ⟨3358017651898675642674401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 143275419814343494087441109 3358017651898675642674401)
                    ·
                      refine ⟨2518513238924006732005801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358017651898675642674401 2518513238924006732005801)
                      ·
                        rfl

theorem cell23_4904787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 3, 7, 2].length) (baseStart_4904787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904787 prefixEnd_4904787 := by exact prefixLift 4904787
  have htrace : WordTrace (prefixWord ++ tailWord_4904787) baseStart_4904787 baseEnd_4904787 := by
    simpa [prefixWord, tailWord_4904787, baseEnd_4904787] using wordTrace_append hprefix tailTrace_4904787
  have hstable : (prefixWord ++ tailWord_4904787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904787).length < 2 ^ (prefixWord ++ tailWord_4904787).sum := by decide
  have hdescent : baseEnd_4904787 < baseStart_4904787 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904807 : List Nat := [1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5]
def baseStart_4904807 : Nat := 118140960795 + 4904807 * 2 ^ 59
def prefixEnd_4904807 : Nat := 4983230072969 + 3 ^ 40 * 4904807 * 2
def baseEnd_4904807 : Nat := 2518523508537096653755709

theorem tailTrace_4904807 : CollatzResearch.WordTrace tailWord_4904807 prefixEnd_4904807 2518523508537096653755709 := by
  unfold tailWord_4904807
  simp only [CollatzResearch.WordTrace]
  refine ⟨178893007941729388190048675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119262005294486258793365783 178893007941729388190048675)
  ·
    refine ⟨268339511912594082285073013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178893007941729388190048675 268339511912594082285073013)
    ·
      refine ⟨25156829241805695214225595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268339511912594082285073013 25156829241805695214225595)
      ·
        refine ⟨37735243862708542821338393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25156829241805695214225595 37735243862708542821338393)
        ·
          refine ⟨28301432897031407116003795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37735243862708542821338393 28301432897031407116003795)
          ·
            refine ⟨42452149345547110674005693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28301432897031407116003795 42452149345547110674005693)
            ·
              refine ⟨15919556004580166502752135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42452149345547110674005693 15919556004580166502752135)
              ·
                refine ⟨23879334006870249754128203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15919556004580166502752135 23879334006870249754128203)
                ·
                  refine ⟨35819001010305374631192305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23879334006870249754128203 35819001010305374631192305)
                  ·
                    refine ⟨26864250757729030973394229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35819001010305374631192305 26864250757729030973394229)
                    ·
                      refine ⟨2518523508537096653755709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26864250757729030973394229 2518523508537096653755709)
                      ·
                        rfl

theorem cell23_4904807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 1, 1, 2, 5].length) (baseStart_4904807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904807 prefixEnd_4904807 := by exact prefixLift 4904807
  have htrace : WordTrace (prefixWord ++ tailWord_4904807) baseStart_4904807 baseEnd_4904807 := by
    simpa [prefixWord, tailWord_4904807, baseEnd_4904807] using wordTrace_append hprefix tailTrace_4904807
  have hstable : (prefixWord ++ tailWord_4904807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904807).length < 2 ^ (prefixWord ++ tailWord_4904807).sum := by decide
  have hdescent : baseEnd_4904807 < baseStart_4904807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904817 : List Nat := [1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 4]
def baseStart_4904817 : Nat := 118140960795 + 4904817 * 2 ^ 59
def prefixEnd_4904817 : Nat := 4983230072969 + 3 ^ 40 * 4904817 * 2
def baseEnd_4904817 : Nat := 2518528643343641614630663

theorem tailTrace_4904817 : CollatzResearch.WordTrace tailWord_4904817 prefixEnd_4904817 2518528643343641614630663 := by
  unfold tailWord_4904817
  simp only [CollatzResearch.WordTrace]
  refine ⟨178893372671693159897912705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119262248447795439931941803 178893372671693159897912705)
  ·
    refine ⟨134170029503769869923434529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178893372671693159897912705 134170029503769869923434529)
    ·
      refine ⟨100627522127827402442575897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134170029503769869923434529 100627522127827402442575897)
      ·
        refine ⟨75470641595870551831931923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100627522127827402442575897 75470641595870551831931923)
        ·
          refine ⟨113205962393805827747897885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75470641595870551831931923 113205962393805827747897885)
          ·
            refine ⟨42452235897677185405461707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113205962393805827747897885 42452235897677185405461707)
            ·
              refine ⟨63678353846515778108192561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42452235897677185405461707 63678353846515778108192561)
              ·
                refine ⟨47758765384886833581144421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63678353846515778108192561 47758765384886833581144421)
                ·
                  refine ⟨8954768509666281296464579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47758765384886833581144421 8954768509666281296464579)
                  ·
                    refine ⟨13432152764499421944696869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8954768509666281296464579 13432152764499421944696869)
                    ·
                      refine ⟨2518528643343641614630663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13432152764499421944696869 2518528643343641614630663)
                      ·
                        rfl

theorem cell23_4904817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 1, 2, 4, 1, 4].length) (baseStart_4904817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904817 prefixEnd_4904817 := by exact prefixLift 4904817
  have htrace : WordTrace (prefixWord ++ tailWord_4904817) baseStart_4904817 baseEnd_4904817 := by
    simpa [prefixWord, tailWord_4904817, baseEnd_4904817] using wordTrace_append hprefix tailTrace_4904817
  have hstable : (prefixWord ++ tailWord_4904817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904817).length < 2 ^ (prefixWord ++ tailWord_4904817).sum := by decide
  have hdescent : baseEnd_4904817 < baseStart_4904817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904827 : List Nat := [1, 1, 1, 1, 1, 5, 1, 3, 5, 4]
def baseStart_4904827 : Nat := 118140960795 + 4904827 * 2 ^ 59
def prefixEnd_4904827 : Nat := 4983230072969 + 3 ^ 40 * 4904827 * 2
def baseEnd_4904827 : Nat := 839511259383395525168539

theorem tailTrace_4904827 : CollatzResearch.WordTrace tailWord_4904827 prefixEnd_4904827 839511259383395525168539 := by
  unfold tailWord_4904827
  simp only [CollatzResearch.WordTrace]
  refine ⟨178893737401656931605776735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119262491601104621070517823 178893737401656931605776735)
  ·
    refine ⟨268340606102485397408665103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178893737401656931605776735 268340606102485397408665103)
    ·
      refine ⟨402510909153728096112997655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268340606102485397408665103 402510909153728096112997655)
      ·
        refine ⟨603766363730592144169496483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402510909153728096112997655 603766363730592144169496483)
        ·
          refine ⟨905649545595888216254244725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603766363730592144169496483 905649545595888216254244725)
          ·
            refine ⟨84904644899614520273835443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 905649545595888216254244725 84904644899614520273835443)
            ·
              refine ⟨127356967349421780410753165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84904644899614520273835443 127356967349421780410753165)
              ·
                refine ⟨47758862756033167654032437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127356967349421780410753165 47758862756033167654032437)
                ·
                  refine ⟨4477393383378109467565541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47758862756033167654032437 4477393383378109467565541)
                  ·
                    refine ⟨839511259383395525168539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4477393383378109467565541 839511259383395525168539)
                    ·
                      rfl

theorem cell23_4904827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 3, 5, 4].length) (baseStart_4904827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904827 prefixEnd_4904827 := by exact prefixLift 4904827
  have htrace : WordTrace (prefixWord ++ tailWord_4904827) baseStart_4904827 baseEnd_4904827 := by
    simpa [prefixWord, tailWord_4904827, baseEnd_4904827] using wordTrace_append hprefix tailTrace_4904827
  have hstable : (prefixWord ++ tailWord_4904827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904827).length < 2 ^ (prefixWord ++ tailWord_4904827).sum := by decide
  have hdescent : baseEnd_4904827 < baseStart_4904827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904857 : List Nat := [1, 2, 1, 2, 1, 3, 3, 4, 6]
def baseStart_4904857 : Nat := 118140960795 + 4904857 * 2 ^ 59
def prefixEnd_4904857 : Nat := 4983230072969 + 3 ^ 40 * 4904857 * 2
def baseEnd_4904857 : Nat := 279838798063313495347831

theorem tailTrace_4904857 : CollatzResearch.WordTrace tailWord_4904857 prefixEnd_4904857 279838798063313495347831 := by
  unfold tailWord_4904857
  simp only [CollatzResearch.WordTrace]
  refine ⟨178894831591548246729368825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119263221061032164486245883 178894831591548246729368825)
  ·
    refine ⟨134171123693661185047026619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178894831591548246729368825 134171123693661185047026619)
    ·
      refine ⟨201256685540491777570539929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134171123693661185047026619 201256685540491777570539929)
      ·
        refine ⟨150942514155368833177904947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201256685540491777570539929 150942514155368833177904947)
        ·
          refine ⟨226413771233053249766857421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150942514155368833177904947 226413771233053249766857421)
          ·
            refine ⟨84905164212394968662571533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226413771233053249766857421 84905164212394968662571533)
            ·
              refine ⟨31839436579648113248464325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84905164212394968662571533 31839436579648113248464325)
              ·
                refine ⟨5969894358684021234087061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31839436579648113248464325 5969894358684021234087061)
                ·
                  refine ⟨279838798063313495347831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5969894358684021234087061 279838798063313495347831)
                  ·
                    rfl

theorem cell23_4904857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 4, 6].length) (baseStart_4904857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904857 prefixEnd_4904857 := by exact prefixLift 4904857
  have htrace : WordTrace (prefixWord ++ tailWord_4904857) baseStart_4904857 baseEnd_4904857 := by
    simpa [prefixWord, tailWord_4904857, baseEnd_4904857] using wordTrace_append hprefix tailTrace_4904857
  have hstable : (prefixWord ++ tailWord_4904857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904857).length < 2 ^ (prefixWord ++ tailWord_4904857).sum := by decide
  have hdescent : baseEnd_4904857 < baseStart_4904857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904867 : List Nat := [1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3]
def baseStart_4904867 : Nat := 118140960795 + 4904867 * 2 ^ 59
def prefixEnd_4904867 : Nat := 4983230072969 + 3 ^ 40 * 4904867 * 2
def baseEnd_4904867 : Nat := 2518554317376366419005433

theorem tailTrace_4904867 : CollatzResearch.WordTrace tailWord_4904867 prefixEnd_4904867 2518554317376366419005433 := by
  unfold tailWord_4904867
  simp only [CollatzResearch.WordTrace]
  refine ⟨178895196321512018437232855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119263464214341345624821903 178895196321512018437232855)
  ·
    refine ⟨268342794482268027655849283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178895196321512018437232855 268342794482268027655849283)
    ·
      refine ⟨402514191723402041483773925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268342794482268027655849283 402514191723402041483773925)
      ·
        refine ⟨75471410948137882778207611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402514191723402041483773925 75471410948137882778207611)
        ·
          refine ⟨113207116422206824167311417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75471410948137882778207611 113207116422206824167311417)
          ·
            refine ⟨84905337316655118125483563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113207116422206824167311417 84905337316655118125483563)
            ·
              refine ⟨127358005974982677188225345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84905337316655118125483563 127358005974982677188225345)
              ·
                refine ⟨95518504481237007891169009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127358005974982677188225345 95518504481237007891169009)
                ·
                  refine ⟨71638878360927755918376757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95518504481237007891169009 71638878360927755918376757)
                  ·
                    refine ⟨6716144846336977117347821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71638878360927755918376757 6716144846336977117347821)
                    ·
                      refine ⟨2518554317376366419005433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716144846336977117347821 2518554317376366419005433)
                      ·
                        rfl

theorem cell23_4904867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 2, 2, 5, 3].length) (baseStart_4904867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904867 prefixEnd_4904867 := by exact prefixLift 4904867
  have htrace : WordTrace (prefixWord ++ tailWord_4904867) baseStart_4904867 baseEnd_4904867 := by
    simpa [prefixWord, tailWord_4904867, baseEnd_4904867] using wordTrace_append hprefix tailTrace_4904867
  have hstable : (prefixWord ++ tailWord_4904867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904867).length < 2 ^ (prefixWord ++ tailWord_4904867).sum := by decide
  have hdescent : baseEnd_4904867 < baseStart_4904867 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904944 : List Nat := [2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3]
def baseStart_4904944 : Nat := 118140960795 + 4904944 * 2 ^ 59
def prefixEnd_4904944 : Nat := 4983230072969 + 3 ^ 40 * 4904944 * 2
def baseEnd_4904944 : Nat := 2518593855386762617742579

theorem tailTrace_4904944 : CollatzResearch.WordTrace tailWord_4904944 prefixEnd_4904944 2518593855386762617742579 := by
  unfold tailWord_4904944
  simp only [CollatzResearch.WordTrace]
  refine ⟨89449002371116530293892943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119265336494822040391857257 89449002371116530293892943)
  ·
    refine ⟨134173503556674795440839415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89449002371116530293892943 134173503556674795440839415)
    ·
      refine ⟨201260255335012193161259123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134173503556674795440839415 201260255335012193161259123)
      ·
        refine ⟨301890383002518289741888685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201260255335012193161259123 301890383002518289741888685)
        ·
          refine ⟨113208893625944358653208257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301890383002518289741888685 113208893625944358653208257)
          ·
            refine ⟨84906670219458268989906193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113208893625944358653208257 84906670219458268989906193)
            ·
              refine ⟨63680002664593701742429645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84906670219458268989906193 63680002664593701742429645)
              ·
                refine ⟨23880000999222638153411117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63680002664593701742429645 23880000999222638153411117)
                ·
                  refine ⟨8955000374708489307529169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23880000999222638153411117 8955000374708489307529169)
                  ·
                    refine ⟨6716250281031366980646877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8955000374708489307529169 6716250281031366980646877)
                    ·
                      refine ⟨2518593855386762617742579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716250281031366980646877 2518593855386762617742579)
                      ·
                        rfl

theorem cell23_4904944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 3, 3, 2, 3].length) (baseStart_4904944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904944 prefixEnd_4904944 := by exact prefixLift 4904944
  have htrace : WordTrace (prefixWord ++ tailWord_4904944) baseStart_4904944 baseEnd_4904944 := by
    simpa [prefixWord, tailWord_4904944, baseEnd_4904944] using wordTrace_append hprefix tailTrace_4904944
  have hstable : (prefixWord ++ tailWord_4904944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904944).length < 2 ^ (prefixWord ++ tailWord_4904944).sum := by decide
  have hdescent : baseEnd_4904944 < baseStart_4904944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904958 : List Nat := [4, 2, 2, 2, 1, 1, 2, 3, 1, 1, 4]
def baseStart_4904958 : Nat := 118140960795 + 4904958 * 2 ^ 59
def prefixEnd_4904958 : Nat := 4983230072969 + 3 ^ 40 * 4904958 * 2
def baseEnd_4904958 : Nat := 2518601044115925562967515

theorem tailTrace_4904958 : CollatzResearch.WordTrace tailWord_4904958 prefixEnd_4904958 2518601044115925562967515 := by
  unfold tailWord_4904958
  simp only [CollatzResearch.WordTrace]
  refine ⟨22362314420522792622349441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119265676909454893985863685 22362314420522792622349441)
  ·
    refine ⟨16771735815392094466762081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22362314420522792622349441 16771735815392094466762081)
    ·
      refine ⟨12578801861544070850071561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16771735815392094466762081 12578801861544070850071561)
      ·
        refine ⟨9434101396158053137553671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12578801861544070850071561 9434101396158053137553671)
        ·
          refine ⟨14151152094237079706330507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9434101396158053137553671 14151152094237079706330507)
          ·
            refine ⟨21226728141355619559495761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14151152094237079706330507 21226728141355619559495761)
            ·
              refine ⟨15920046106016714669621821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21226728141355619559495761 15920046106016714669621821)
              ·
                refine ⟨5970017289756268001108183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15920046106016714669621821 5970017289756268001108183)
                ·
                  refine ⟨8955025934634402001662275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970017289756268001108183 8955025934634402001662275)
                  ·
                    refine ⟨13432538901951603002493413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8955025934634402001662275 13432538901951603002493413)
                    ·
                      refine ⟨2518601044115925562967515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13432538901951603002493413 2518601044115925562967515)
                      ·
                        rfl

theorem cell23_4904958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 1, 1, 2, 3, 1, 1, 4].length) (baseStart_4904958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904958 prefixEnd_4904958 := by exact prefixLift 4904958
  have htrace : WordTrace (prefixWord ++ tailWord_4904958) baseStart_4904958 baseEnd_4904958 := by
    simpa [prefixWord, tailWord_4904958, baseEnd_4904958] using wordTrace_append hprefix tailTrace_4904958
  have hstable : (prefixWord ++ tailWord_4904958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904958).length < 2 ^ (prefixWord ++ tailWord_4904958).sum := by decide
  have hdescent : baseEnd_4904958 < baseStart_4904958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904961 : List Nat := [1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 3]
def baseStart_4904961 : Nat := 118140960795 + 4904961 * 2 ^ 59
def prefixEnd_4904961 : Nat := 4983230072969 + 3 ^ 40 * 4904961 * 2
def baseEnd_4904961 : Nat := 2518602584557889051230001

theorem tailTrace_4904961 : CollatzResearch.WordTrace tailWord_4904961 prefixEnd_4904961 2518602584557889051230001 := by
  unfold tailWord_4904961
  simp only [CollatzResearch.WordTrace]
  refine ⟨178898624783171472491154737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119265749855447648327436491 178898624783171472491154737)
  ·
    refine ⟨134173968587378604368366053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178898624783171472491154737 134173968587378604368366053)
    ·
      refine ⟨25157619110133488319068635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134173968587378604368366053 25157619110133488319068635)
      ·
        refine ⟨37736428665200232478602953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25157619110133488319068635 37736428665200232478602953)
        ·
          refine ⟨28302321498900174358952215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37736428665200232478602953 28302321498900174358952215)
          ·
            refine ⟨42453482248350261538428323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28302321498900174358952215 42453482248350261538428323)
            ·
              refine ⟨63680223372525392307642485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42453482248350261538428323 63680223372525392307642485)
              ·
                refine ⟨5970020941174255528841483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63680223372525392307642485 5970020941174255528841483)
                ·
                  refine ⟨8955031411761383293262225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970020941174255528841483 8955031411761383293262225)
                  ·
                    refine ⟨6716273558821037469946669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8955031411761383293262225 6716273558821037469946669)
                    ·
                      refine ⟨2518602584557889051230001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716273558821037469946669 2518602584557889051230001)
                      ·
                        rfl

theorem cell23_4904961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 5, 1, 2, 3].length) (baseStart_4904961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904961 prefixEnd_4904961 := by exact prefixLift 4904961
  have htrace : WordTrace (prefixWord ++ tailWord_4904961) baseStart_4904961 baseEnd_4904961 := by
    simpa [prefixWord, tailWord_4904961, baseEnd_4904961] using wordTrace_append hprefix tailTrace_4904961
  have hstable : (prefixWord ++ tailWord_4904961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904961).length < 2 ^ (prefixWord ++ tailWord_4904961).sum := by decide
  have hdescent : baseEnd_4904961 < baseStart_4904961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4904987 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5]
def baseStart_4904987 : Nat := 118140960795 + 4904987 * 2 ^ 59
def prefixEnd_4904987 : Nat := 4983230072969 + 3 ^ 40 * 4904987 * 2
def baseEnd_4904987 : Nat := 2518615935054905949504881

theorem tailTrace_4904987 : CollatzResearch.WordTrace tailWord_4904987 prefixEnd_4904987 2518615935054905949504881 := by
  unfold tailWord_4904987
  simp only [CollatzResearch.WordTrace]
  refine ⟨178899573081077278931601215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119266382054051519287734143 178899573081077278931601215)
  ·
    refine ⟨268349359621615918397401823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178899573081077278931601215 268349359621615918397401823)
    ·
      refine ⟨402524039432423877596102735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268349359621615918397401823 402524039432423877596102735)
      ·
        refine ⟨603786059148635816394154103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402524039432423877596102735 603786059148635816394154103)
        ·
          refine ⟨905679088722953724591231155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603786059148635816394154103 905679088722953724591231155)
          ·
            refine ⟨1358518633084430586886846733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905679088722953724591231155 1358518633084430586886846733)
            ·
              refine ⟨509444487406661470082567525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1358518633084430586886846733 509444487406661470082567525)
              ·
                refine ⟨95520841388749025640481411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509444487406661470082567525 95520841388749025640481411)
                ·
                  refine ⟨143281262083123538460722117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95520841388749025640481411 143281262083123538460722117)
                  ·
                    refine ⟨26865236640585663461385397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 143281262083123538460722117 26865236640585663461385397)
                    ·
                      refine ⟨2518615935054905949504881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26865236640585663461385397 2518615935054905949504881)
                      ·
                        rfl

theorem cell23_4904987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 4, 5].length) (baseStart_4904987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4904987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4904987 prefixEnd_4904987 := by exact prefixLift 4904987
  have htrace : WordTrace (prefixWord ++ tailWord_4904987) baseStart_4904987 baseEnd_4904987 := by
    simpa [prefixWord, tailWord_4904987, baseEnd_4904987] using wordTrace_append hprefix tailTrace_4904987
  have hstable : (prefixWord ++ tailWord_4904987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4904987).length < 2 ^ (prefixWord ++ tailWord_4904987).sum := by decide
  have hdescent : baseEnd_4904987 < baseStart_4904987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4904987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905007 : List Nat := [1, 1, 2, 1, 2, 1, 1, 3, 3, 8]
def baseStart_4905007 : Nat := 118140960795 + 4905007 * 2 ^ 59
def prefixEnd_4905007 : Nat := 4983230072969 + 3 ^ 40 * 4905007 * 2
def baseEnd_4905007 : Nat := 839542068222665290418263

theorem tailTrace_4905007 : CollatzResearch.WordTrace tailWord_4905007 prefixEnd_4905007 839542068222665290418263 := by
  unfold tailWord_4905007
  simp only [CollatzResearch.WordTrace]
  refine ⟨178900302541004822347329275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119266868360669881564886183 178900302541004822347329275)
  ·
    refine ⟨268350453811507233520993913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178900302541004822347329275 268350453811507233520993913)
    ·
      refine ⟨201262840358630425140745435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268350453811507233520993913 201262840358630425140745435)
      ·
        refine ⟨301894260537945637711118153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201262840358630425140745435 301894260537945637711118153)
        ·
          refine ⟨226420695403459228283338615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301894260537945637711118153 226420695403459228283338615)
          ·
            refine ⟨339631043105188842425007923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226420695403459228283338615 339631043105188842425007923)
            ·
              refine ⟨509446564657783263637511885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339631043105188842425007923 509446564657783263637511885)
              ·
                refine ⟨191042461746668723864066957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 509446564657783263637511885 191042461746668723864066957)
                ·
                  refine ⟨71640923155000771449025109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191042461746668723864066957 71640923155000771449025109)
                  ·
                    refine ⟨839542068222665290418263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 71640923155000771449025109 839542068222665290418263)
                    ·
                      rfl

theorem cell23_4905007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 1, 3, 3, 8].length) (baseStart_4905007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905007 prefixEnd_4905007 := by exact prefixLift 4905007
  have htrace : WordTrace (prefixWord ++ tailWord_4905007) baseStart_4905007 baseEnd_4905007 := by
    simpa [prefixWord, tailWord_4905007, baseEnd_4905007] using wordTrace_append hprefix tailTrace_4905007
  have hstable : (prefixWord ++ tailWord_4905007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905007).length < 2 ^ (prefixWord ++ tailWord_4905007).sum := by decide
  have hdescent : baseEnd_4905007 < baseStart_4905007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905012 : List Nat := [2, 5, 1, 2, 2, 1, 3, 1, 1, 2, 3]
def baseStart_4905012 : Nat := 118140960795 + 4905012 * 2 ^ 59
def prefixEnd_4905012 : Nat := 4983230072969 + 3 ^ 40 * 4905012 * 2
def baseEnd_4905012 : Nat := 2518628772071268351692267

theorem tailTrace_4905012 : CollatzResearch.WordTrace tailWord_4905012 prefixEnd_4905012 2518628772071268351692267 := by
  unfold tailWord_4905012
  simp only [CollatzResearch.WordTrace]
  refine ⟨89450242452993354100630645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119266989937324472134174193 89450242452993354100630645)
  ·
    refine ⟨8385960229968126946934123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89450242452993354100630645 8385960229968126946934123)
    ·
      refine ⟨12578940344952190420401185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8385960229968126946934123 12578940344952190420401185)
      ·
        refine ⟨9434205258714142815300889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12578940344952190420401185 9434205258714142815300889)
        ·
          refine ⟨7075653944035607111475667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9434205258714142815300889 7075653944035607111475667)
          ·
            refine ⟨10613480916053410667213501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7075653944035607111475667 10613480916053410667213501)
            ·
              refine ⟨3980055343520029000205063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10613480916053410667213501 3980055343520029000205063)
              ·
                refine ⟨5970083015280043500307595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980055343520029000205063 5970083015280043500307595)
                ·
                  refine ⟨8955124522920065250461393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970083015280043500307595 8955124522920065250461393)
                  ·
                    refine ⟨6716343392190048937846045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8955124522920065250461393 6716343392190048937846045)
                    ·
                      refine ⟨2518628772071268351692267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716343392190048937846045 2518628772071268351692267)
                      ·
                        rfl

theorem cell23_4905012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 3, 1, 1, 2, 3].length) (baseStart_4905012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905012 prefixEnd_4905012 := by exact prefixLift 4905012
  have htrace : WordTrace (prefixWord ++ tailWord_4905012) baseStart_4905012 baseEnd_4905012 := by
    simpa [prefixWord, tailWord_4905012, baseEnd_4905012] using wordTrace_append hprefix tailTrace_4905012
  have hstable : (prefixWord ++ tailWord_4905012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905012).length < 2 ^ (prefixWord ++ tailWord_4905012).sum := by decide
  have hdescent : baseEnd_4905012 < baseStart_4905012 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905025 : List Nat := [1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 3]
def baseStart_4905025 : Nat := 118140960795 + 4905025 * 2 ^ 59
def prefixEnd_4905025 : Nat := 4983230072969 + 3 ^ 40 * 4905025 * 2
def baseEnd_4905025 : Nat := 2518635447319776800829707

theorem tailTrace_4905025 : CollatzResearch.WordTrace tailWord_4905025 prefixEnd_4905025 2518635447319776800829707 := by
  unfold tailWord_4905025
  simp only [CollatzResearch.WordTrace]
  refine ⟨178900959054939611421484529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119267306036626407614323019 178900959054939611421484529)
  ·
    refine ⟨134175719291204708566113397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178900959054939611421484529 134175719291204708566113397)
    ·
      refine ⟨12578973683550441428073131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134175719291204708566113397 12578973683550441428073131)
      ·
        refine ⟨18868460525325662142109697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12578973683550441428073131 18868460525325662142109697)
        ·
          refine ⟨14151345393994246606582273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18868460525325662142109697 14151345393994246606582273)
          ·
            refine ⟨10613509045495684954936705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14151345393994246606582273 10613509045495684954936705)
            ·
              refine ⟨7960131784121763716202529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10613509045495684954936705 7960131784121763716202529)
              ·
                refine ⟨5970098838091322787151897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7960131784121763716202529 5970098838091322787151897)
                ·
                  refine ⟨4477574128568492090363923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5970098838091322787151897 4477574128568492090363923)
                  ·
                    refine ⟨6716361192852738135545885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4477574128568492090363923 6716361192852738135545885)
                    ·
                      refine ⟨2518635447319776800829707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716361192852738135545885 2518635447319776800829707)
                      ·
                        rfl

theorem cell23_4905025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 2, 2, 2, 1, 3].length) (baseStart_4905025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905025 prefixEnd_4905025 := by exact prefixLift 4905025
  have htrace : WordTrace (prefixWord ++ tailWord_4905025) baseStart_4905025 baseEnd_4905025 := by
    simpa [prefixWord, tailWord_4905025, baseEnd_4905025] using wordTrace_append hprefix tailTrace_4905025
  have hstable : (prefixWord ++ tailWord_4905025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905025).length < 2 ^ (prefixWord ++ tailWord_4905025).sum := by decide
  have hdescent : baseEnd_4905025 < baseStart_4905025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905031 : List Nat := [1, 1, 4, 1, 3, 1, 1, 2, 3, 4, 2]
def baseStart_4905031 : Nat := 118140960795 + 4905031 * 2 ^ 59
def prefixEnd_4905031 : Nat := 4983230072969 + 3 ^ 40 * 4905031 * 2
def baseEnd_4905031 : Nat := 2518638528203703777354679

theorem tailTrace_4905031 : CollatzResearch.WordTrace tailWord_4905031 prefixEnd_4905031 2518638528203703777354679 := by
  unfold tailWord_4905031
  simp only [CollatzResearch.WordTrace]
  refine ⟨178901177892917874446202947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119267451928611916297468631 178901177892917874446202947)
  ·
    refine ⟨268351766839376811669304421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178901177892917874446202947 268351766839376811669304421)
    ·
      refine ⟨50315956282383152187994579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268351766839376811669304421 50315956282383152187994579)
      ·
        refine ⟨75473934423574728281991869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50315956282383152187994579 75473934423574728281991869)
        ·
          refine ⟨28302725408840523105746951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75473934423574728281991869 28302725408840523105746951)
          ·
            refine ⟨42454088113260784658620427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28302725408840523105746951 42454088113260784658620427)
            ·
              refine ⟨63681132169891176987930641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42454088113260784658620427 63681132169891176987930641)
              ·
                refine ⟨47760849127418382740947981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63681132169891176987930641 47760849127418382740947981)
                ·
                  refine ⟨17910318422781893527855493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47760849127418382740947981 17910318422781893527855493)
                  ·
                    refine ⟨3358184704271605036472905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17910318422781893527855493 3358184704271605036472905)
                    ·
                      refine ⟨2518638528203703777354679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358184704271605036472905 2518638528203703777354679)
                      ·
                        rfl

theorem cell23_4905031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 1, 2, 3, 4, 2].length) (baseStart_4905031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905031 prefixEnd_4905031 := by exact prefixLift 4905031
  have htrace : WordTrace (prefixWord ++ tailWord_4905031) baseStart_4905031 baseEnd_4905031 := by
    simpa [prefixWord, tailWord_4905031, baseEnd_4905031] using wordTrace_append hprefix tailTrace_4905031
  have hstable : (prefixWord ++ tailWord_4905031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905031).length < 2 ^ (prefixWord ++ tailWord_4905031).sum := by decide
  have hdescent : baseEnd_4905031 < baseStart_4905031 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905048 : List Nat := [2, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2]
def baseStart_4905048 : Nat := 118140960795 + 4905048 * 2 ^ 59
def prefixEnd_4905048 : Nat := 4983230072969 + 3 ^ 40 * 4905048 * 2
def baseEnd_4905048 : Nat := 2518647257374830210842101

theorem tailTrace_4905048 : CollatzResearch.WordTrace tailWord_4905048 prefixEnd_4905048 2518647257374830210842101 := by
  unfold tailWord_4905048
  simp only [CollatzResearch.WordTrace]
  refine ⟨89450898966928143174785899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119267865289237524233047865 89450898966928143174785899)
  ·
    refine ⟨134176348450392214762178849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89450898966928143174785899 134176348450392214762178849)
    ·
      refine ⟨100632261337794161071634137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134176348450392214762178849 100632261337794161071634137)
      ·
        refine ⟨75474196003345620803725603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100632261337794161071634137 75474196003345620803725603)
        ·
          refine ⟨113211294005018431205588405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75474196003345620803725603 113211294005018431205588405)
          ·
            refine ⟨10613558812970477925523913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113211294005018431205588405 10613558812970477925523913)
            ·
              refine ⟨7960169109727858444142935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10613558812970477925523913 7960169109727858444142935)
              ·
                refine ⟨11940253664591787666214403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7960169109727858444142935 11940253664591787666214403)
                ·
                  refine ⟨17910380496887681499321605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11940253664591787666214403 17910380496887681499321605)
                  ·
                    refine ⟨3358196343166440281122801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17910380496887681499321605 3358196343166440281122801)
                    ·
                      refine ⟨2518647257374830210842101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358196343166440281122801 2518647257374830210842101)
                      ·
                        rfl

theorem cell23_4905048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 2, 1, 1, 4, 2].length) (baseStart_4905048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905048 prefixEnd_4905048 := by exact prefixLift 4905048
  have htrace : WordTrace (prefixWord ++ tailWord_4905048) baseStart_4905048 baseEnd_4905048 := by
    simpa [prefixWord, tailWord_4905048, baseEnd_4905048] using wordTrace_append hprefix tailTrace_4905048
  have hstable : (prefixWord ++ tailWord_4905048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905048).length < 2 ^ (prefixWord ++ tailWord_4905048).sum := by decide
  have hdescent : baseEnd_4905048 < baseStart_4905048 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905071 : List Nat := [1, 1, 2, 1, 3, 4, 1, 5, 5]
def baseStart_4905071 : Nat := 118140960795 + 4905071 * 2 ^ 59
def prefixEnd_4905071 : Nat := 4983230072969 + 3 ^ 40 * 4905071 * 2
def baseEnd_4905071 : Nat := 279851007492209291206055

theorem tailTrace_4905071 : CollatzResearch.WordTrace tailWord_4905071 prefixEnd_4905071 279851007492209291206055 := by
  unfold tailWord_4905071
  simp only [CollatzResearch.WordTrace]
  refine ⟨178902636812772961277659067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119268424541848640851772711 178902636812772961277659067)
  ·
    refine ⟨268353955219159441916488601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178902636812772961277659067 268353955219159441916488601)
    ·
      refine ⟨201265466414369581437366451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268353955219159441916488601 201265466414369581437366451)
      ·
        refine ⟨301898199621554372156049677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201265466414369581437366451 301898199621554372156049677)
        ·
          refine ⟨113211824858082889558518629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301898199621554372156049677 113211824858082889558518629)
          ·
            refine ⟨21227217160890541792222243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113211824858082889558518629 21227217160890541792222243)
            ·
              refine ⟨31840825741335812688333365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21227217160890541792222243 31840825741335812688333365)
              ·
                refine ⟨2985077413250232439531253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31840825741335812688333365 2985077413250232439531253)
                ·
                  refine ⟨279851007492209291206055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2985077413250232439531253 279851007492209291206055)
                  ·
                    rfl

theorem cell23_4905071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 1, 5, 5].length) (baseStart_4905071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905071 prefixEnd_4905071 := by exact prefixLift 4905071
  have htrace : WordTrace (prefixWord ++ tailWord_4905071) baseStart_4905071 baseEnd_4905071 := by
    simpa [prefixWord, tailWord_4905071, baseEnd_4905071] using wordTrace_append hprefix tailTrace_4905071
  have hstable : (prefixWord ++ tailWord_4905071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905071).length < 2 ^ (prefixWord ++ tailWord_4905071).sum := by decide
  have hdescent : baseEnd_4905071 < baseStart_4905071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905081 : List Nat := [1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 3]
def baseStart_4905081 : Nat := 118140960795 + 4905081 * 2 ^ 59
def prefixEnd_4905081 : Nat := 4983230072969 + 3 ^ 40 * 4905081 * 2
def baseEnd_4905081 : Nat := 2518664202236428581729449

theorem tailTrace_4905081 : CollatzResearch.WordTrace tailWord_4905081 prefixEnd_4905081 2518664202236428581729449 := by
  unfold tailWord_4905081
  simp only [CollatzResearch.WordTrace]
  refine ⟨178903001542736732985523097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119268667695157821990348731 178903001542736732985523097)
  ·
    refine ⟨134177251157052549739142323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178903001542736732985523097 134177251157052549739142323)
    ·
      refine ⟨201265876735578824608713485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134177251157052549739142323 201265876735578824608713485)
      ·
        refine ⟨75474703775842059228267557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201265876735578824608713485 75474703775842059228267557)
        ·
          refine ⟨14151506957970386105300167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75474703775842059228267557 14151506957970386105300167)
          ·
            refine ⟨21227260436955579157950251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14151506957970386105300167 21227260436955579157950251)
            ·
              refine ⟨31840890655433368736925377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21227260436955579157950251 31840890655433368736925377)
              ·
                refine ⟨23880667991575026552694033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31840890655433368736925377 23880667991575026552694033)
                ·
                  refine ⟨17910500993681269914520525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23880667991575026552694033 17910500993681269914520525)
                  ·
                    refine ⟨6716437872630476217945197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17910500993681269914520525 6716437872630476217945197)
                    ·
                      refine ⟨2518664202236428581729449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716437872630476217945197 2518664202236428581729449)
                      ·
                        rfl

theorem cell23_4905081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 2, 2, 3, 3].length) (baseStart_4905081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905081 prefixEnd_4905081 := by exact prefixLift 4905081
  have htrace : WordTrace (prefixWord ++ tailWord_4905081) baseStart_4905081 baseEnd_4905081 := by
    simpa [prefixWord, tailWord_4905081, baseEnd_4905081] using wordTrace_append hprefix tailTrace_4905081
  have hstable : (prefixWord ++ tailWord_4905081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905081).length < 2 ^ (prefixWord ++ tailWord_4905081).sum := by decide
  have hdescent : baseEnd_4905081 < baseStart_4905081 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905104 : List Nat := [2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4]
def baseStart_4905104 : Nat := 118140960795 + 4905104 * 2 ^ 59
def prefixEnd_4905104 : Nat := 4983230072969 + 3 ^ 40 * 4905104 * 2
def baseEnd_4905104 : Nat := 2518676012291481991741843

theorem tailTrace_4905104 : CollatzResearch.WordTrace tailWord_4905104 prefixEnd_4905104 2518676012291481991741843 := by
  unfold tailWord_4905104
  simp only [CollatzResearch.WordTrace]
  refine ⟨89451920210826703956805183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119269226947768938609073577 89451920210826703956805183)
  ·
    refine ⟨134177880316240055935207775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89451920210826703956805183 134177880316240055935207775)
    ·
      refine ⟨201266820474360083902811663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134177880316240055935207775 201266820474360083902811663)
      ·
        refine ⟨301900230711540125854217495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201266820474360083902811663 301900230711540125854217495)
        ·
          refine ⟨452850346067310188781326243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301900230711540125854217495 452850346067310188781326243)
          ·
            refine ⟨679275519100965283171989365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452850346067310188781326243 679275519100965283171989365)
            ·
              refine ⟨63682079915715495297374003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 679275519100965283171989365 63682079915715495297374003)
              ·
                refine ⟨95523119873573242946061005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63682079915715495297374003 95523119873573242946061005)
                ·
                  refine ⟨35821169952589966104772877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95523119873573242946061005 35821169952589966104772877)
                  ·
                    refine ⟨13432938732221237289289829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35821169952589966104772877 13432938732221237289289829)
                    ·
                      refine ⟨2518676012291481991741843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13432938732221237289289829 2518676012291481991741843)
                      ·
                        rfl

theorem cell23_4905104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 5, 1, 3, 3, 4].length) (baseStart_4905104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905104 prefixEnd_4905104 := by exact prefixLift 4905104
  have htrace : WordTrace (prefixWord ++ tailWord_4905104) baseStart_4905104 baseEnd_4905104 := by
    simpa [prefixWord, tailWord_4905104, baseEnd_4905104] using wordTrace_append hprefix tailTrace_4905104
  have hstable : (prefixWord ++ tailWord_4905104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905104).length < 2 ^ (prefixWord ++ tailWord_4905104).sum := by decide
  have hdescent : baseEnd_4905104 < baseStart_4905104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905121 : List Nat := [1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 4]
def baseStart_4905121 : Nat := 118140960795 + 4905121 * 2 ^ 59
def prefixEnd_4905121 : Nat := 4983230072969 + 3 ^ 40 * 4905121 * 2
def baseEnd_4905121 : Nat := 2518684741462608425229265

theorem tailTrace_4905121 : CollatzResearch.WordTrace tailWord_4905121 prefixEnd_4905121 2518684741462608425229265 := by
  unfold tailWord_4905121
  simp only [CollatzResearch.WordTrace]
  refine ⟨178904460462591819816979217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119269640308394546544652811 178904460462591819816979217)
  ·
    refine ⟨134178345346943864862734413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178904460462591819816979217 134178345346943864862734413)
    ·
      refine ⟨50316879505103949323525405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134178345346943864862734413 50316879505103949323525405)
      ·
        refine ⟨18868829814413980996322027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50316879505103949323525405 18868829814413980996322027)
        ·
          refine ⟨28303244721620971494483041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18868829814413980996322027 28303244721620971494483041)
          ·
            refine ⟨21227433541215728620862281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28303244721620971494483041 21227433541215728620862281)
            ·
              refine ⟨15920575155911796465646711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21227433541215728620862281 15920575155911796465646711)
              ·
                refine ⟨23880862733867694698470067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15920575155911796465646711 23880862733867694698470067)
                ·
                  refine ⟨35821294100801542047705101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23880862733867694698470067 35821294100801542047705101)
                  ·
                    refine ⟨13432985287800578267889413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35821294100801542047705101 13432985287800578267889413)
                    ·
                      refine ⟨2518684741462608425229265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13432985287800578267889413 2518684741462608425229265)
                      ·
                        rfl

theorem cell23_4905121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 2, 2, 1, 1, 3, 4].length) (baseStart_4905121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905121 prefixEnd_4905121 := by exact prefixLift 4905121
  have htrace : WordTrace (prefixWord ++ tailWord_4905121) baseStart_4905121 baseEnd_4905121 := by
    simpa [prefixWord, tailWord_4905121, baseEnd_4905121] using wordTrace_append hprefix tailTrace_4905121
  have hstable : (prefixWord ++ tailWord_4905121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905121).length < 2 ^ (prefixWord ++ tailWord_4905121).sum := by decide
  have hdescent : baseEnd_4905121 < baseStart_4905121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905144 : List Nat := [2, 1, 2, 1, 2, 1, 3, 3, 8]
def baseStart_4905144 : Nat := 118140960795 + 4905144 * 2 ^ 59
def prefixEnd_4905144 : Nat := 4983230072969 + 3 ^ 40 * 4905144 * 2
def baseEnd_4905144 : Nat := 279855172390851315026851

theorem tailTrace_4905144 : CollatzResearch.WordTrace tailWord_4905144 prefixEnd_4905144 279855172390851315026851 := by
  unfold tailWord_4905144
  simp only [CollatzResearch.WordTrace]
  refine ⟨89452649670754247372533243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119270199561005663163377657 89452649670754247372533243)
  ·
    refine ⟨134178974506131371058799865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89452649670754247372533243 134178974506131371058799865)
    ·
      refine ⟨100634230879598528294099899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134178974506131371058799865 100634230879598528294099899)
      ·
        refine ⟨150951346319397792441149849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100634230879598528294099899 150951346319397792441149849)
        ·
          refine ⟨113213509739548344330862387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150951346319397792441149849 113213509739548344330862387)
          ·
            refine ⟨169820264609322516496293581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113213509739548344330862387 169820264609322516496293581)
            ·
              refine ⟨63682599228495943686110093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169820264609322516496293581 63682599228495943686110093)
              ·
                refine ⟨23880974710685978882291285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63682599228495943686110093 23880974710685978882291285)
                ·
                  refine ⟨279855172390851315026851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23880974710685978882291285 279855172390851315026851)
                  ·
                    rfl

theorem cell23_4905144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 3, 8].length) (baseStart_4905144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905144 prefixEnd_4905144 := by exact prefixLift 4905144
  have htrace : WordTrace (prefixWord ++ tailWord_4905144) baseStart_4905144 baseEnd_4905144 := by
    simpa [prefixWord, tailWord_4905144, baseEnd_4905144] using wordTrace_append hprefix tailTrace_4905144
  have hstable : (prefixWord ++ tailWord_4905144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905144).length < 2 ^ (prefixWord ++ tailWord_4905144).sum := by decide
  have hdescent : baseEnd_4905144 < baseStart_4905144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905198 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_4905198 : Nat := 118140960795 + 4905198 * 2 ^ 59
def prefixEnd_4905198 : Nat := 4983230072969 + 3 ^ 40 * 4905198 * 2
def baseEnd_4905198 : Nat := 2518724279473004623966411

theorem tailTrace_4905198 : CollatzResearch.WordTrace tailWord_4905198 prefixEnd_4905198 2518724279473004623966411 := by
  unfold tailWord_4905198
  simp only [CollatzResearch.WordTrace]
  refine ⟨22363408610414107745941531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119271512588875241311688165 22363408610414107745941531)
  ·
    refine ⟨33545112915621161618912297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22363408610414107745941531 33545112915621161618912297)
    ·
      refine ⟨25158834686715871214184223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33545112915621161618912297 25158834686715871214184223)
      ·
        refine ⟨37738252030073806821276335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25158834686715871214184223 37738252030073806821276335)
        ·
          refine ⟨56607378045110710231914503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37738252030073806821276335 56607378045110710231914503)
          ·
            refine ⟨84911067067666065347871755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56607378045110710231914503 84911067067666065347871755)
            ·
              refine ⟨127366600601499098021807633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84911067067666065347871755 127366600601499098021807633)
              ·
                refine ⟨95524950451124323516355725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127366600601499098021807633 95524950451124323516355725)
                ·
                  refine ⟨35821856419171621318633397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95524950451124323516355725 35821856419171621318633397)
                  ·
                    refine ⟨3358299039297339498621881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35821856419171621318633397 3358299039297339498621881)
                    ·
                      refine ⟨2518724279473004623966411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358299039297339498621881 2518724279473004623966411)
                      ·
                        rfl

theorem cell23_4905198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_4905198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905198 prefixEnd_4905198 := by exact prefixLift 4905198
  have htrace : WordTrace (prefixWord ++ tailWord_4905198) baseStart_4905198 baseEnd_4905198 := by
    simpa [prefixWord, tailWord_4905198, baseEnd_4905198] using wordTrace_append hprefix tailTrace_4905198
  have hstable : (prefixWord ++ tailWord_4905198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905198).length < 2 ^ (prefixWord ++ tailWord_4905198).sum := by decide
  have hdescent : baseEnd_4905198 < baseStart_4905198 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905228 : List Nat := [2, 2, 1, 2, 2, 2, 2, 4, 1, 1, 4]
def baseStart_4905228 : Nat := 118140960795 + 4905228 * 2 ^ 59
def prefixEnd_4905228 : Nat := 4983230072969 + 3 ^ 40 * 4905228 * 2
def baseEnd_4905228 : Nat := 2518739683892639506591273

theorem tailTrace_4905228 : CollatzResearch.WordTrace tailWord_4905228 prefixEnd_4905228 2518739683892639506591273 := by
  unfold tailWord_4905228
  simp only [CollatzResearch.WordTrace]
  refine ⟨89454181536602088545562169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119272242048802784727416225 89454181536602088545562169)
  ·
    refine ⟨67090636152451566409171627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89454181536602088545562169 67090636152451566409171627)
    ·
      refine ⟨100635954228677349613757441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67090636152451566409171627 100635954228677349613757441)
      ·
        refine ⟨75476965671508012210318081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100635954228677349613757441 75476965671508012210318081)
        ·
          refine ⟨56607724253631009157738561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75476965671508012210318081 56607724253631009157738561)
          ·
            refine ⟨42455793190223256868303921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56607724253631009157738561 42455793190223256868303921)
            ·
              refine ⟨31841844892667442651227941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42455793190223256868303921 31841844892667442651227941)
              ·
                refine ⟨5970345917375145497105239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31841844892667442651227941 5970345917375145497105239)
                ·
                  refine ⟨8955518876062718245657859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970345917375145497105239 8955518876062718245657859)
                  ·
                    refine ⟨13433278314094077368486789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8955518876062718245657859 13433278314094077368486789)
                    ·
                      refine ⟨2518739683892639506591273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13433278314094077368486789 2518739683892639506591273)
                      ·
                        rfl

theorem cell23_4905228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 4, 1, 1, 4].length) (baseStart_4905228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905228 prefixEnd_4905228 := by exact prefixLift 4905228
  have htrace : WordTrace (prefixWord ++ tailWord_4905228) baseStart_4905228 baseEnd_4905228 := by
    simpa [prefixWord, tailWord_4905228, baseEnd_4905228] using wordTrace_append hprefix tailTrace_4905228
  have hstable : (prefixWord ++ tailWord_4905228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905228).length < 2 ^ (prefixWord ++ tailWord_4905228).sum := by decide
  have hdescent : baseEnd_4905228 < baseStart_4905228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905242 : List Nat := [3, 1, 1, 3, 4, 2, 2, 1, 1, 5]
def baseStart_4905242 : Nat := 118140960795 + 4905242 * 2 ^ 59
def prefixEnd_4905242 : Nat := 4983230072969 + 3 ^ 40 * 4905242 * 2
def baseEnd_4905242 : Nat := 839582290873934150605403

theorem tailTrace_4905242 : CollatzResearch.WordTrace tailWord_4905242 prefixEnd_4905242 839582290873934150605403 := by
  unfold tailWord_4905242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44727218423788364370533495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119272582463435638321422653 44727218423788364370533495)
  ·
    refine ⟨67090827635682546555800243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44727218423788364370533495 67090827635682546555800243)
    ·
      refine ⟨100636241453523819833700365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67090827635682546555800243 100636241453523819833700365)
      ·
        refine ⟨37738590545071432437637637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100636241453523819833700365 37738590545071432437637637)
        ·
          refine ⟨7075985727200893582057057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37738590545071432437637637 7075985727200893582057057)
          ·
            refine ⟨5306989295400670186542793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7075985727200893582057057 5306989295400670186542793)
            ·
              refine ⟨3980241971550502639907095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5306989295400670186542793 3980241971550502639907095)
              ·
                refine ⟨5970362957325753959860643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980241971550502639907095 5970362957325753959860643)
                ·
                  refine ⟨8955544435988630939790965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970362957325753959860643 8955544435988630939790965)
                  ·
                    refine ⟨839582290873934150605403, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8955544435988630939790965 839582290873934150605403)
                    ·
                      rfl

theorem cell23_4905242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 2, 2, 1, 1, 5].length) (baseStart_4905242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905242 prefixEnd_4905242 := by exact prefixLift 4905242
  have htrace : WordTrace (prefixWord ++ tailWord_4905242) baseStart_4905242 baseEnd_4905242 := by
    simpa [prefixWord, tailWord_4905242, baseEnd_4905242] using wordTrace_append hprefix tailTrace_4905242
  have hstable : (prefixWord ++ tailWord_4905242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905242).length < 2 ^ (prefixWord ++ tailWord_4905242).sum := by decide
  have hdescent : baseEnd_4905242 < baseStart_4905242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905311 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 4, 6]
def baseStart_4905311 : Nat := 118140960795 + 4905311 * 2 ^ 59
def prefixEnd_4905311 : Nat := 4983230072969 + 3 ^ 40 * 4905311 * 2
def baseEnd_4905311 : Nat := 839594100928987560617797

theorem tailTrace_4905311 : CollatzResearch.WordTrace tailWord_4905311 prefixEnd_4905311 839594100928987560617797 := by
  unfold tailWord_4905311
  simp only [CollatzResearch.WordTrace]
  refine ⟨178911390331903482266395787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119274260221268988177597191 178911390331903482266395787)
  ·
    refine ⟨268367085497855223399593681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178911390331903482266395787 268367085497855223399593681)
    ·
      refine ⟨201275314123391417549695261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268367085497855223399593681 201275314123391417549695261)
      ·
        refine ⟨75478242796271781581135723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201275314123391417549695261 75478242796271781581135723)
        ·
          refine ⟨113217364194407672371703585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75478242796271781581135723 113217364194407672371703585)
          ·
            refine ⟨84913023145805754278777689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113217364194407672371703585 84913023145805754278777689)
            ·
              refine ⟨63684767359354315709083267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84913023145805754278777689 63684767359354315709083267)
              ·
                refine ⟨95527151039031473563624901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63684767359354315709083267 95527151039031473563624901)
                ·
                  refine ⟨17911340819818401293179669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95527151039031473563624901 17911340819818401293179669)
                  ·
                    refine ⟨839594100928987560617797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17911340819818401293179669 839594100928987560617797)
                    ·
                      rfl

theorem cell23_4905311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 4, 6].length) (baseStart_4905311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905311 prefixEnd_4905311 := by exact prefixLift 4905311
  have htrace : WordTrace (prefixWord ++ tailWord_4905311) baseStart_4905311 baseEnd_4905311 := by
    simpa [prefixWord, tailWord_4905311, baseEnd_4905311] using wordTrace_append hprefix tailTrace_4905311
  have hstable : (prefixWord ++ tailWord_4905311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905311).length < 2 ^ (prefixWord ++ tailWord_4905311).sum := by decide
  have hdescent : baseEnd_4905311 < baseStart_4905311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905321 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 5]
def baseStart_4905321 : Nat := 118140960795 + 4905321 * 2 ^ 59
def prefixEnd_4905321 : Nat := 4983230072969 + 3 ^ 40 * 4905321 * 2
def baseEnd_4905321 : Nat := 2518787437593507642728345

theorem tailTrace_4905321 : CollatzResearch.WordTrace tailWord_4905321 prefixEnd_4905321 2518787437593507642728345 := by
  unfold tailWord_4905321
  simp only [CollatzResearch.WordTrace]
  refine ⟨178911755061867253974259817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119274503374578169316173211 178911755061867253974259817)
  ·
    refine ⟨134183816296400440480694863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178911755061867253974259817 134183816296400440480694863)
    ·
      refine ⟨201275724444600660721042295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134183816296400440480694863 201275724444600660721042295)
      ·
        refine ⟨301913586666900991081563443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201275724444600660721042295 301913586666900991081563443)
        ·
          refine ⟨452870380000351486622345165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301913586666900991081563443 452870380000351486622345165)
          ·
            refine ⟨169826392500131807483379437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 452870380000351486622345165 169826392500131807483379437)
            ·
              refine ⟨63684897187549427806267289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169826392500131807483379437 63684897187549427806267289)
              ·
                refine ⟨47763672890662070854700467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63684897187549427806267289 47763672890662070854700467)
                ·
                  refine ⟨71645509335993106282050701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47763672890662070854700467 71645509335993106282050701)
                  ·
                    refine ⟨26867066000997414855769013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71645509335993106282050701 26867066000997414855769013)
                    ·
                      refine ⟨2518787437593507642728345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26867066000997414855769013 2518787437593507642728345)
                      ·
                        rfl

theorem cell23_4905321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 3, 5].length) (baseStart_4905321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905321 prefixEnd_4905321 := by exact prefixLift 4905321
  have htrace : WordTrace (prefixWord ++ tailWord_4905321) baseStart_4905321 baseEnd_4905321 := by
    simpa [prefixWord, tailWord_4905321, baseEnd_4905321] using wordTrace_append hprefix tailTrace_4905321
  have hstable : (prefixWord ++ tailWord_4905321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905321).length < 2 ^ (prefixWord ++ tailWord_4905321).sum := by decide
  have hdescent : baseEnd_4905321 < baseStart_4905321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905335 : List Nat := [1, 1, 3, 1, 1, 2, 2, 2, 6, 2, 2]
def baseStart_4905335 : Nat := 118140960795 + 4905335 * 2 ^ 59
def prefixEnd_4905335 : Nat := 4983230072969 + 3 ^ 40 * 4905335 * 2
def baseEnd_4905335 : Nat := 2518794626322670587953281

theorem tailTrace_4905335 : CollatzResearch.WordTrace tailWord_4905335 prefixEnd_4905335 2518794626322670587953281 := by
  unfold tailWord_4905335
  simp only [CollatzResearch.WordTrace]
  refine ⟨178912265683816534365269459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119274843789211022910179639 178912265683816534365269459)
  ·
    refine ⟨268368398525724801547904189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178912265683816534365269459 268368398525724801547904189)
    ·
      refine ⟨100638149447146800580464071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268368398525724801547904189 100638149447146800580464071)
      ·
        refine ⟨150957224170720200870696107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100638149447146800580464071 150957224170720200870696107)
        ·
          refine ⟨226435836256080301306044161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150957224170720200870696107 226435836256080301306044161)
          ·
            refine ⟨169826877192060225979533121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226435836256080301306044161 169826877192060225979533121)
            ·
              refine ⟨127370157894045169484649841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169826877192060225979533121 127370157894045169484649841)
              ·
                refine ⟨95527618420533877113487381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127370157894045169484649841 95527618420533877113487381)
                ·
                  refine ⟨4477857113462525489694721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 95527618420533877113487381 4477857113462525489694721)
                  ·
                    refine ⟨3358392835096894117271041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4477857113462525489694721 3358392835096894117271041)
                    ·
                      refine ⟨2518794626322670587953281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358392835096894117271041 2518794626322670587953281)
                      ·
                        rfl

theorem cell23_4905335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 2, 6, 2, 2].length) (baseStart_4905335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905335 prefixEnd_4905335 := by exact prefixLift 4905335
  have htrace : WordTrace (prefixWord ++ tailWord_4905335) baseStart_4905335 baseEnd_4905335 := by
    simpa [prefixWord, tailWord_4905335, baseEnd_4905335] using wordTrace_append hprefix tailTrace_4905335
  have hstable : (prefixWord ++ tailWord_4905335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905335).length < 2 ^ (prefixWord ++ tailWord_4905335).sum := by decide
  have hdescent : baseEnd_4905335 < baseStart_4905335 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905361 : List Nat := [1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 6]
def baseStart_4905361 : Nat := 118140960795 + 4905361 * 2 ^ 59
def prefixEnd_4905361 : Nat := 4983230072969 + 3 ^ 40 * 4905361 * 2
def baseEnd_4905361 : Nat := 2518807976819687486228161

theorem tailTrace_4905361 : CollatzResearch.WordTrace tailWord_4905361 prefixEnd_4905361 2518807976819687486228161 := by
  unfold tailWord_4905361
  simp only [CollatzResearch.WordTrace]
  refine ⟨178913213981722340805715937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119275475987814893870477291 178913213981722340805715937)
  ·
    refine ⟨134184910486291755604286953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178913213981722340805715937 134184910486291755604286953)
    ·
      refine ⟨100638682864718816703215215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134184910486291755604286953 100638682864718816703215215)
      ·
        refine ⟨150958024297078225054822823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100638682864718816703215215 150958024297078225054822823)
        ·
          refine ⟨226437036445617337582234235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150958024297078225054822823 226437036445617337582234235)
          ·
            refine ⟨339655554668426006373351353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226437036445617337582234235 339655554668426006373351353)
            ·
              refine ⟨254741666001319504780013515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339655554668426006373351353 254741666001319504780013515)
              ·
                refine ⟨382112499001979257170020273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254741666001319504780013515 382112499001979257170020273)
                ·
                  refine ⟨286584374251484442877515205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382112499001979257170020273 286584374251484442877515205)
                  ·
                    refine ⟨53734570172153333039534101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286584374251484442877515205 53734570172153333039534101)
                    ·
                      refine ⟨2518807976819687486228161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53734570172153333039534101 2518807976819687486228161)
                      ·
                        rfl

theorem cell23_4905361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 6].length) (baseStart_4905361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905361 prefixEnd_4905361 := by exact prefixLift 4905361
  have htrace : WordTrace (prefixWord ++ tailWord_4905361) baseStart_4905361 baseEnd_4905361 := by
    simpa [prefixWord, tailWord_4905361, baseEnd_4905361] using wordTrace_append hprefix tailTrace_4905361
  have hstable : (prefixWord ++ tailWord_4905361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905361).length < 2 ^ (prefixWord ++ tailWord_4905361).sum := by decide
  have hdescent : baseEnd_4905361 < baseStart_4905361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905375 : List Nat := [1, 1, 2, 5, 1, 1, 3, 4, 5]
def baseStart_4905375 : Nat := 118140960795 + 4905375 * 2 ^ 59
def prefixEnd_4905375 : Nat := 4983230072969 + 3 ^ 40 * 4905375 * 2
def baseEnd_4905375 : Nat := 279868351727650047939233

theorem tailTrace_4905375 : CollatzResearch.WordTrace tailWord_4905375 prefixEnd_4905375 279868351727650047939233 := by
  unfold tailWord_4905375
  simp only [CollatzResearch.WordTrace]
  refine ⟨178913724603671621196725579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119275816402447747464483719 178913724603671621196725579)
  ·
    refine ⟨268370586905507431795088369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178913724603671621196725579 268370586905507431795088369)
    ·
      refine ⟨201277940179130573846316277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268370586905507431795088369 201277940179130573846316277)
      ·
        refine ⟨18869806891793491298092151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201277940179130573846316277 18869806891793491298092151)
        ·
          refine ⟨28304710337690236947138227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18869806891793491298092151 28304710337690236947138227)
          ·
            refine ⟨42457065506535355420707341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28304710337690236947138227 42457065506535355420707341)
            ·
              refine ⟨15921399564950758282765253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42457065506535355420707341 15921399564950758282765253)
              ·
                refine ⟨2985262418428267178018485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15921399564950758282765253 2985262418428267178018485)
                ·
                  refine ⟨279868351727650047939233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2985262418428267178018485 279868351727650047939233)
                  ·
                    rfl

theorem cell23_4905375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 3, 4, 5].length) (baseStart_4905375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905375 prefixEnd_4905375 := by exact prefixLift 4905375
  have htrace : WordTrace (prefixWord ++ tailWord_4905375) baseStart_4905375 baseEnd_4905375 := by
    simpa [prefixWord, tailWord_4905375, baseEnd_4905375] using wordTrace_append hprefix tailTrace_4905375
  have hstable : (prefixWord ++ tailWord_4905375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905375).length < 2 ^ (prefixWord ++ tailWord_4905375).sum := by decide
  have hdescent : baseEnd_4905375 < baseStart_4905375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905405 : List Nat := [1, 4, 1, 2, 2, 2, 3, 1, 2, 5]
def baseStart_4905405 : Nat := 118140960795 + 4905405 * 2 ^ 59
def prefixEnd_4905405 : Nat := 4983230072969 + 3 ^ 40 * 4905405 * 2
def baseEnd_4905405 : Nat := 839610189989495104692653

theorem tailTrace_4905405 : CollatzResearch.WordTrace tailWord_4905405 prefixEnd_4905405 839610189989495104692653 := by
  unfold tailWord_4905405
  simp only [CollatzResearch.WordTrace]
  refine ⟨178914818793562936320317669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119276545862375290880211779 178914818793562936320317669)
  ·
    refine ⟨33546528523793050560059563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178914818793562936320317669 33546528523793050560059563)
    ·
      refine ⟨50319792785689575840089345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33546528523793050560059563 50319792785689575840089345)
      ·
        refine ⟨37739844589267181880067009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50319792785689575840089345 37739844589267181880067009)
        ·
          refine ⟨28304883441950386410050257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37739844589267181880067009 28304883441950386410050257)
          ·
            refine ⟨21228662581462789807537693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28304883441950386410050257 21228662581462789807537693)
            ·
              refine ⟨7960748468048546177826635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21228662581462789807537693 7960748468048546177826635)
              ·
                refine ⟨11941122702072819266739953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7960748468048546177826635 11941122702072819266739953)
                ·
                  refine ⟨8955842026554614450054965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11941122702072819266739953 8955842026554614450054965)
                  ·
                    refine ⟨839610189989495104692653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8955842026554614450054965 839610189989495104692653)
                    ·
                      rfl

theorem cell23_4905405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 3, 1, 2, 5].length) (baseStart_4905405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905405 prefixEnd_4905405 := by exact prefixLift 4905405
  have htrace : WordTrace (prefixWord ++ tailWord_4905405) baseStart_4905405 baseEnd_4905405 := by
    simpa [prefixWord, tailWord_4905405, baseEnd_4905405] using wordTrace_append hprefix tailTrace_4905405
  have hstable : (prefixWord ++ tailWord_4905405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905405).length < 2 ^ (prefixWord ++ tailWord_4905405).sum := by decide
  have hdescent : baseEnd_4905405 < baseStart_4905405 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905462 : List Nat := [5, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3]
def baseStart_4905462 : Nat := 118140960795 + 4905462 * 2 ^ 59
def prefixEnd_4905462 : Nat := 4983230072969 + 3 ^ 40 * 4905462 * 2
def baseEnd_4905462 : Nat := 2518859838365791591065197

theorem tailTrace_4905462 : CollatzResearch.WordTrace tailWord_4905462 prefixEnd_4905462 2518859838365791591065197 := by
  unfold tailWord_4905462
  simp only [CollatzResearch.WordTrace]
  refine ⟨11182306109647277190946415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119277931836237623370095093 11182306109647277190946415)
  ·
    refine ⟨16773459164470915786419623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11182306109647277190946415 16773459164470915786419623)
    ·
      refine ⟨25160188746706373679629435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16773459164470915786419623 25160188746706373679629435)
      ·
        refine ⟨37740283120059560519444153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25160188746706373679629435 37740283120059560519444153)
        ·
          refine ⟨28305212340044670389583115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37740283120059560519444153 28305212340044670389583115)
          ·
            refine ⟨42457818510067005584374673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28305212340044670389583115 42457818510067005584374673)
            ·
              refine ⟨31843363882550254188281005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42457818510067005584374673 31843363882550254188281005)
              ·
                refine ⟨11941261455956345320605377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31843363882550254188281005 11941261455956345320605377)
                ·
                  refine ⟨8955946091967258990454033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11941261455956345320605377 8955946091967258990454033)
                  ·
                    refine ⟨6716959568975444242840525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8955946091967258990454033 6716959568975444242840525)
                    ·
                      refine ⟨2518859838365791591065197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6716959568975444242840525 2518859838365791591065197)
                      ·
                        rfl

theorem cell23_4905462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 2, 3, 2, 2, 3].length) (baseStart_4905462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905462 prefixEnd_4905462 := by exact prefixLift 4905462
  have htrace : WordTrace (prefixWord ++ tailWord_4905462) baseStart_4905462 baseEnd_4905462 := by
    simpa [prefixWord, tailWord_4905462, baseEnd_4905462] using wordTrace_append hprefix tailTrace_4905462
  have hstable : (prefixWord ++ tailWord_4905462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905462).length < 2 ^ (prefixWord ++ tailWord_4905462).sum := by decide
  have hdescent : baseEnd_4905462 < baseStart_4905462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905486 : List Nat := [4, 1, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_4905486 : Nat := 118140960795 + 4905486 * 2 ^ 59
def prefixEnd_4905486 : Nat := 4983230072969 + 3 ^ 40 * 4905486 * 2
def baseEnd_4905486 : Nat := 839624053967166499055029

theorem tailTrace_4905486 : CollatzResearch.WordTrace tailWord_4905486 prefixEnd_4905486 839624053967166499055029 := by
  unfold tailWord_4905486
  simp only [CollatzResearch.WordTrace]
  refine ⟨22364721638283685894252039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119278515404179658102677541 22364721638283685894252039)
  ·
    refine ⟨33547082457425528841378059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22364721638283685894252039 33547082457425528841378059)
    ·
      refine ⟨50320623686138293262067089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33547082457425528841378059 50320623686138293262067089)
      ·
        refine ⟨37740467764603719946550317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50320623686138293262067089 37740467764603719946550317)
        ·
          refine ⟨14152675411726394979956369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37740467764603719946550317 14152675411726394979956369)
          ·
            refine ⟨10614506558794796234967277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14152675411726394979956369 10614506558794796234967277)
            ·
              refine ⟨3980439959548048588112729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10614506558794796234967277 3980439959548048588112729)
              ·
                refine ⟨2985329969661036441084547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980439959548048588112729 2985329969661036441084547)
                ·
                  refine ⟨4477994954491554661626821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985329969661036441084547 4477994954491554661626821)
                  ·
                    refine ⟨839624053967166499055029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4477994954491554661626821 839624053967166499055029)
                    ·
                      rfl

theorem cell23_4905486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_4905486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905486 prefixEnd_4905486 := by exact prefixLift 4905486
  have htrace : WordTrace (prefixWord ++ tailWord_4905486) baseStart_4905486 baseEnd_4905486 := by
    simpa [prefixWord, tailWord_4905486, baseEnd_4905486] using wordTrace_append hprefix tailTrace_4905486
  have hstable : (prefixWord ++ tailWord_4905486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905486).length < 2 ^ (prefixWord ++ tailWord_4905486).sum := by decide
  have hdescent : baseEnd_4905486 < baseStart_4905486 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905512 : List Nat := [2, 1, 5, 2, 1, 2, 1, 1, 3, 5]
def baseStart_4905512 : Nat := 118140960795 + 4905512 * 2 ^ 59
def prefixEnd_4905512 : Nat := 4983230072969 + 3 ^ 40 * 4905512 * 2
def baseEnd_4905512 : Nat := 839628504132838798479989

theorem tailTrace_4905512 : CollatzResearch.WordTrace tailWord_4905512 prefixEnd_4905512 839628504132838798479989 := by
  unfold tailWord_4905512
  simp only [CollatzResearch.WordTrace]
  refine ⟨89459360702087646797231395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119279147602783529062975193 89459360702087646797231395)
  ·
    refine ⟨134189041053131470195847093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89459360702087646797231395 134189041053131470195847093)
    ·
      refine ⟨12580222598731075330860665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134189041053131470195847093 12580222598731075330860665)
      ·
        refine ⟨9435166949048306498145499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12580222598731075330860665 9435166949048306498145499)
        ·
          refine ⟨14152750423572459747218249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435166949048306498145499 14152750423572459747218249)
          ·
            refine ⟨10614562817679344810413687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14152750423572459747218249 10614562817679344810413687)
            ·
              refine ⟨15921844226519017215620531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10614562817679344810413687 15921844226519017215620531)
              ·
                refine ⟨23882766339778525823430797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15921844226519017215620531 23882766339778525823430797)
                ·
                  refine ⟨8956037377416947183786549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23882766339778525823430797 8956037377416947183786549)
                  ·
                    refine ⟨839628504132838798479989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8956037377416947183786549 839628504132838798479989)
                    ·
                      rfl

theorem cell23_4905512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 1, 3, 5].length) (baseStart_4905512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905512 prefixEnd_4905512 := by exact prefixLift 4905512
  have htrace : WordTrace (prefixWord ++ tailWord_4905512) baseStart_4905512 baseEnd_4905512 := by
    simpa [prefixWord, tailWord_4905512, baseEnd_4905512] using wordTrace_append hprefix tailTrace_4905512
  have hstable : (prefixWord ++ tailWord_4905512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905512).length < 2 ^ (prefixWord ++ tailWord_4905512).sum := by decide
  have hdescent : baseEnd_4905512 < baseStart_4905512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905515 : List Nat := [1, 1, 1, 1, 2, 1, 3, 3, 2, 6, 2]
def baseStart_4905515 : Nat := 118140960795 + 4905515 * 2 ^ 59
def prefixEnd_4905515 : Nat := 4983230072969 + 3 ^ 40 * 4905515 * 2
def baseEnd_4905515 : Nat := 2518887052840479883702453

theorem tailTrace_4905515 : CollatzResearch.WordTrace tailWord_4905515 prefixEnd_4905515 2518887052840479883702453 := by
  unfold tailWord_4905515
  simp only [CollatzResearch.WordTrace]
  refine ⟨178918830823164425106821999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119279220548776283404547999 178918830823164425106821999)
  ·
    refine ⟨268378246234746637660232999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178918830823164425106821999 268378246234746637660232999)
    ·
      refine ⟨402567369352119956490349499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268378246234746637660232999 402567369352119956490349499)
      ·
        refine ⟨603851054028179934735524249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402567369352119956490349499 603851054028179934735524249)
        ·
          refine ⟨452888290521134951051643187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 603851054028179934735524249 452888290521134951051643187)
          ·
            refine ⟨679332435781702426577464781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452888290521134951051643187 679332435781702426577464781)
            ·
              refine ⟨254749663418138409966549293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 679332435781702426577464781 254749663418138409966549293)
              ·
                refine ⟨95531123781801903737455985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254749663418138409966549293 95531123781801903737455985)
                ·
                  refine ⟨71648342836351427803091989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95531123781801903737455985 71648342836351427803091989)
                  ·
                    refine ⟨3358516070453973178269937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71648342836351427803091989 3358516070453973178269937)
                    ·
                      refine ⟨2518887052840479883702453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358516070453973178269937 2518887052840479883702453)
                      ·
                        rfl

theorem cell23_4905515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 3, 2, 6, 2].length) (baseStart_4905515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905515 prefixEnd_4905515 := by exact prefixLift 4905515
  have htrace : WordTrace (prefixWord ++ tailWord_4905515) baseStart_4905515 baseEnd_4905515 := by
    simpa [prefixWord, tailWord_4905515, baseEnd_4905515] using wordTrace_append hprefix tailTrace_4905515
  have hstable : (prefixWord ++ tailWord_4905515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905515).length < 2 ^ (prefixWord ++ tailWord_4905515).sum := by decide
  have hdescent : baseEnd_4905515 < baseStart_4905515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905525 : List Nat := [1, 3, 3, 1, 1, 2, 3, 2, 1, 6]
def baseStart_4905525 : Nat := 118140960795 + 4905525 * 2 ^ 59
def prefixEnd_4905525 : Nat := 4983230072969 + 3 ^ 40 * 4905525 * 2
def baseEnd_4905525 : Nat := 839630729215674948192469

theorem tailTrace_4905525 : CollatzResearch.WordTrace tailWord_4905525 prefixEnd_4905525 839630729215674948192469 := by
  unfold tailWord_4905525
  simp only [CollatzResearch.WordTrace]
  refine ⟨178919195553128196814686029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119279463702085464543124019 178919195553128196814686029)
  ·
    refine ⟨67094698332423073805507261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178919195553128196814686029 67094698332423073805507261)
    ·
      refine ⟨25160511874658652677065223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67094698332423073805507261 25160511874658652677065223)
      ·
        refine ⟨37740767811987979015597835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25160511874658652677065223 37740767811987979015597835)
        ·
          refine ⟨56611151717981968523396753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37740767811987979015597835 56611151717981968523396753)
          ·
            refine ⟨42458363788486476392547565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56611151717981968523396753 42458363788486476392547565)
            ·
              refine ⟨15921886420682428647205337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42458363788486476392547565 15921886420682428647205337)
              ·
                refine ⟨11941414815511821485404003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15921886420682428647205337 11941414815511821485404003)
                ·
                  refine ⟨17912122223267732228106005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11941414815511821485404003 17912122223267732228106005)
                  ·
                    refine ⟨839630729215674948192469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17912122223267732228106005 839630729215674948192469)
                    ·
                      rfl

theorem cell23_4905525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 2, 1, 6].length) (baseStart_4905525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905525 prefixEnd_4905525 := by exact prefixLift 4905525
  have htrace : WordTrace (prefixWord ++ tailWord_4905525) baseStart_4905525 baseEnd_4905525 := by
    simpa [prefixWord, tailWord_4905525, baseEnd_4905525] using wordTrace_append hprefix tailTrace_4905525
  have hstable : (prefixWord ++ tailWord_4905525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905525).length < 2 ^ (prefixWord ++ tailWord_4905525).sum := by decide
  have hdescent : baseEnd_4905525 < baseStart_4905525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905543 : List Nat := [1, 1, 4, 1, 4, 3, 2, 2, 1, 1, 3]
def baseStart_4905543 : Nat := 118140960795 + 4905543 * 2 ^ 59
def prefixEnd_4905543 : Nat := 4983230072969 + 3 ^ 40 * 4905543 * 2
def baseEnd_4905543 : Nat := 2518901430298805774152325

theorem tailTrace_4905543 : CollatzResearch.WordTrace tailWord_4905543 prefixEnd_4905543 2518901430298805774152325 := by
  unfold tailWord_4905543
  simp only [CollatzResearch.WordTrace]
  refine ⟨178919852067062985888841283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119279901378041990592560855 178919852067062985888841283)
  ·
    refine ⟨268379778100594478833261925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178919852067062985888841283 268379778100594478833261925)
    ·
      refine ⟨50321208393861464781236611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268379778100594478833261925 50321208393861464781236611)
      ·
        refine ⟨75481812590792197171854917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50321208393861464781236611 75481812590792197171854917)
        ·
          refine ⟨14152839860773536969722797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75481812590792197171854917 14152839860773536969722797)
          ·
            refine ⟨5307314947790076363646049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14152839860773536969722797 5307314947790076363646049)
            ·
              refine ⟨3980486210842557272734537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5307314947790076363646049 3980486210842557272734537)
              ·
                refine ⟨2985364658131917954550903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980486210842557272734537 2985364658131917954550903)
                ·
                  refine ⟨4478046987197876931826355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985364658131917954550903 4478046987197876931826355)
                  ·
                    refine ⟨6717070480796815397739533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4478046987197876931826355 6717070480796815397739533)
                    ·
                      refine ⟨2518901430298805774152325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6717070480796815397739533 2518901430298805774152325)
                      ·
                        rfl

theorem cell23_4905543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 3, 2, 2, 1, 1, 3].length) (baseStart_4905543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905543 prefixEnd_4905543 := by exact prefixLift 4905543
  have htrace : WordTrace (prefixWord ++ tailWord_4905543) baseStart_4905543 baseEnd_4905543 := by
    simpa [prefixWord, tailWord_4905543, baseEnd_4905543] using wordTrace_append hprefix tailTrace_4905543
  have hstable : (prefixWord ++ tailWord_4905543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905543).length < 2 ^ (prefixWord ++ tailWord_4905543).sum := by decide
  have hdescent : baseEnd_4905543 < baseStart_4905543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905570 : List Nat := [3, 3, 2, 3, 2, 1, 1, 1, 2, 3, 2]
def baseStart_4905570 : Nat := 118140960795 + 4905570 * 2 ^ 59
def prefixEnd_4905570 : Nat := 4983230072969 + 3 ^ 40 * 4905570 * 2
def baseEnd_4905570 : Nat := 2518915294276477168514701

theorem tailTrace_4905570 : CollatzResearch.WordTrace tailWord_4905570 prefixEnd_4905570 2518915294276477168514701 := by
  unfold tailWord_4905570
  simp only [CollatzResearch.WordTrace]
  refine ⟨44730209209491292375018541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119280557891976779666716109 44730209209491292375018541)
  ·
    refine ⟨16773828453559234640631953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44730209209491292375018541 16773828453559234640631953)
    ·
      refine ⟨12580371340169425980473965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16773828453559234640631953 12580371340169425980473965)
      ·
        refine ⟨4717639252563534742677737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12580371340169425980473965 4717639252563534742677737)
        ·
          refine ⟨3538229439422651057008303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4717639252563534742677737 3538229439422651057008303)
          ·
            refine ⟨5307344159133976585512455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538229439422651057008303 5307344159133976585512455)
            ·
              refine ⟨7961016238700964878268683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307344159133976585512455 7961016238700964878268683)
              ·
                refine ⟨11941524358051447317403025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7961016238700964878268683 11941524358051447317403025)
                ·
                  refine ⟨8956143268538585488052269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11941524358051447317403025 8956143268538585488052269)
                  ·
                    refine ⟨3358553725701969558019601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8956143268538585488052269 3358553725701969558019601)
                    ·
                      refine ⟨2518915294276477168514701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358553725701969558019601 2518915294276477168514701)
                      ·
                        rfl

theorem cell23_4905570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_4905570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905570 prefixEnd_4905570 := by exact prefixLift 4905570
  have htrace : WordTrace (prefixWord ++ tailWord_4905570) baseStart_4905570 baseEnd_4905570 := by
    simpa [prefixWord, tailWord_4905570, baseEnd_4905570] using wordTrace_append hprefix tailTrace_4905570
  have hstable : (prefixWord ++ tailWord_4905570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905570).length < 2 ^ (prefixWord ++ tailWord_4905570).sum := by decide
  have hdescent : baseEnd_4905570 < baseStart_4905570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905625 : List Nat := [1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 5]
def baseStart_4905625 : Nat := 118140960795 + 4905625 * 2 ^ 59
def prefixEnd_4905625 : Nat := 4983230072969 + 3 ^ 40 * 4905625 * 2
def baseEnd_4905625 : Nat := 2518943535712474453326947

theorem tailTrace_4905625 : CollatzResearch.WordTrace tailWord_4905625 prefixEnd_4905625 2518943535712474453326947 := by
  unfold tailWord_4905625
  simp only [CollatzResearch.WordTrace]
  refine ⟨178922842852765913893326329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119281895235177275928884219 178922842852765913893326329)
  ·
    refine ⟨134192132139574435419994747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178922842852765913893326329 134192132139574435419994747)
    ·
      refine ⟨201288198209361653129992121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134192132139574435419994747 201288198209361653129992121)
      ·
        refine ⟨150966148657021239847494091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201288198209361653129992121 150966148657021239847494091)
        ·
          refine ⟨226449222985531859771241137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 150966148657021239847494091 226449222985531859771241137)
          ·
            refine ⟨169836917239148894828430853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226449222985531859771241137 169836917239148894828430853)
            ·
              refine ⟨31844421982340417780330785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169836917239148894828430853 31844421982340417780330785)
              ·
                refine ⟨23883316486755313335248089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31844421982340417780330785 23883316486755313335248089)
                ·
                  refine ⟨17912487365066485001436067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23883316486755313335248089 17912487365066485001436067)
                  ·
                    refine ⟨26868731047599727502154101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17912487365066485001436067 26868731047599727502154101)
                    ·
                      refine ⟨2518943535712474453326947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26868731047599727502154101 2518943535712474453326947)
                      ·
                        rfl

theorem cell23_4905625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 2, 2, 1, 5].length) (baseStart_4905625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905625 prefixEnd_4905625 := by exact prefixLift 4905625
  have htrace : WordTrace (prefixWord ++ tailWord_4905625) baseStart_4905625 baseEnd_4905625 := by
    simpa [prefixWord, tailWord_4905625, baseEnd_4905625] using wordTrace_append hprefix tailTrace_4905625
  have hstable : (prefixWord ++ tailWord_4905625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905625).length < 2 ^ (prefixWord ++ tailWord_4905625).sum := by decide
  have hdescent : baseEnd_4905625 < baseStart_4905625 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905635 : List Nat := [1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4]
def baseStart_4905635 : Nat := 118140960795 + 4905635 * 2 ^ 59
def prefixEnd_4905635 : Nat := 4983230072969 + 3 ^ 40 * 4905635 * 2
def baseEnd_4905635 : Nat := 2518948670519019414201901

theorem tailTrace_4905635 : CollatzResearch.WordTrace tailWord_4905635 prefixEnd_4905635 2518948670519019414201901 := by
  unfold tailWord_4905635
  simp only [CollatzResearch.WordTrace]
  refine ⟨178923207582729685601190359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119282138388486457067460239 178923207582729685601190359)
  ·
    refine ⟨268384811374094528401785539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178923207582729685601190359 268384811374094528401785539)
    ·
      refine ⟨402577217061141792602678309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268384811374094528401785539 402577217061141792602678309)
      ·
        refine ⟨75483228198964086113002183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402577217061141792602678309 75483228198964086113002183)
        ·
          refine ⟨113224842298446129169503275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75483228198964086113002183 113224842298446129169503275)
          ·
            refine ⟨169837263447669193754254913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113224842298446129169503275 169837263447669193754254913)
            ·
              refine ⟨127377947585751895315691185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169837263447669193754254913 127377947585751895315691185)
              ·
                refine ⟨95533460689313921486768389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127377947585751895315691185 95533460689313921486768389)
                ·
                  refine ⟨17912523879246360278769073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 95533460689313921486768389 17912523879246360278769073)
                  ·
                    refine ⟨13434392909434770209076805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17912523879246360278769073 13434392909434770209076805)
                    ·
                      refine ⟨2518948670519019414201901, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13434392909434770209076805 2518948670519019414201901)
                      ·
                        rfl

theorem cell23_4905635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 2, 2, 4, 2, 4].length) (baseStart_4905635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905635 prefixEnd_4905635 := by exact prefixLift 4905635
  have htrace : WordTrace (prefixWord ++ tailWord_4905635) baseStart_4905635 baseEnd_4905635 := by
    simpa [prefixWord, tailWord_4905635, baseEnd_4905635] using wordTrace_append hprefix tailTrace_4905635
  have hstable : (prefixWord ++ tailWord_4905635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905635).length < 2 ^ (prefixWord ++ tailWord_4905635).sum := by decide
  have hdescent : baseEnd_4905635 < baseStart_4905635 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905677 : List Nat := [1, 6, 2, 1, 3, 1, 1, 2, 1, 3, 2]
def baseStart_4905677 : Nat := 118140960795 + 4905677 * 2 ^ 59
def prefixEnd_4905677 : Nat := 4983230072969 + 3 ^ 40 * 4905677 * 2
def baseEnd_4905677 : Nat := 2518970236706508249876709

theorem tailTrace_4905677 : CollatzResearch.WordTrace tailWord_4905677 prefixEnd_4905677 2518970236706508249876709 := by
  unfold tailWord_4905677
  simp only [CollatzResearch.WordTrace]
  refine ⟨178924739448577526774219285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119283159632385017849479523 178924739448577526774219285)
  ·
    refine ⟨8387097161652071567541529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 178924739448577526774219285 8387097161652071567541529)
    ·
      refine ⟨6290322871239053675656147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8387097161652071567541529 6290322871239053675656147)
      ·
        refine ⟨9435484306858580513484221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290322871239053675656147 9435484306858580513484221)
        ·
          refine ⟨3538306615071967692556583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9435484306858580513484221 3538306615071967692556583)
          ·
            refine ⟨5307459922607951538834875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538306615071967692556583 5307459922607951538834875)
            ·
              refine ⟨7961189883911927308252313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307459922607951538834875 7961189883911927308252313)
              ·
                refine ⟨5970892412933945481189235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7961189883911927308252313 5970892412933945481189235)
                ·
                  refine ⟨8956338619400918221783853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5970892412933945481189235 8956338619400918221783853)
                  ·
                    refine ⟨3358626982275344333168945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8956338619400918221783853 3358626982275344333168945)
                    ·
                      refine ⟨2518970236706508249876709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358626982275344333168945 2518970236706508249876709)
                      ·
                        rfl

theorem cell23_4905677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 3, 1, 1, 2, 1, 3, 2].length) (baseStart_4905677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905677 prefixEnd_4905677 := by exact prefixLift 4905677
  have htrace : WordTrace (prefixWord ++ tailWord_4905677) baseStart_4905677 baseEnd_4905677 := by
    simpa [prefixWord, tailWord_4905677, baseEnd_4905677] using wordTrace_append hprefix tailTrace_4905677
  have hstable : (prefixWord ++ tailWord_4905677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905677).length < 2 ^ (prefixWord ++ tailWord_4905677).sum := by decide
  have hdescent : baseEnd_4905677 < baseStart_4905677 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905712 : List Nat := [2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4]
def baseStart_4905712 : Nat := 118140960795 + 4905712 * 2 ^ 59
def prefixEnd_4905712 : Nat := 4983230072969 + 3 ^ 40 * 4905712 * 2
def baseEnd_4905712 : Nat := 2518988208529415612939047

theorem tailTrace_4905712 : CollatzResearch.WordTrace tailWord_4905712 prefixEnd_4905712 2518988208529415612939047 := by
  unfold tailWord_4905712
  simp only [CollatzResearch.WordTrace]
  refine ⟨89463008001725363875871695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119284010668967151834495593 89463008001725363875871695)
  ·
    refine ⟨134194512002588045813807543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89463008001725363875871695 134194512002588045813807543)
    ·
      refine ⟨201291768003882068720711315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134194512002588045813807543 201291768003882068720711315)
      ·
        refine ⟨301937652005823103081066973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201291768003882068720711315 301937652005823103081066973)
        ·
          refine ⟨113226619502183663655400115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301937652005823103081066973 113226619502183663655400115)
          ·
            refine ⟨169839929253275495483100173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113226619502183663655400115 169839929253275495483100173)
            ·
              refine ⟨63689973469978310806162565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169839929253275495483100173 63689973469978310806162565)
              ·
                refine ⟨11941870025620933276155481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63689973469978310806162565 11941870025620933276155481)
                ·
                  refine ⟨8956402519215699957116611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11941870025620933276155481 8956402519215699957116611)
                  ·
                    refine ⟨13434603778823549935674917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8956402519215699957116611 13434603778823549935674917)
                    ·
                      refine ⟨2518988208529415612939047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13434603778823549935674917 2518988208529415612939047)
                      ·
                        rfl

theorem cell23_4905712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 4, 2, 1, 4].length) (baseStart_4905712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905712 prefixEnd_4905712 := by exact prefixLift 4905712
  have htrace : WordTrace (prefixWord ++ tailWord_4905712) baseStart_4905712 baseEnd_4905712 := by
    simpa [prefixWord, tailWord_4905712, baseEnd_4905712] using wordTrace_append hprefix tailTrace_4905712
  have hstable : (prefixWord ++ tailWord_4905712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905712).length < 2 ^ (prefixWord ++ tailWord_4905712).sum := by decide
  have hdescent : baseEnd_4905712 < baseStart_4905712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905715 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5]
def baseStart_4905715 : Nat := 118140960795 + 4905715 * 2 ^ 59
def prefixEnd_4905715 : Nat := 4983230072969 + 3 ^ 40 * 4905715 * 2
def baseEnd_4905715 : Nat := 2518989748971379101201533

theorem tailTrace_4905715 : CollatzResearch.WordTrace tailWord_4905715 prefixEnd_4905715 2518989748971379101201533 := by
  unfold tailWord_4905715
  simp only [CollatzResearch.WordTrace]
  refine ⟨178926125422439859264102599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119284083614959906176068399 178926125422439859264102599)
  ·
    refine ⟨268389188133659788896153899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178926125422439859264102599 268389188133659788896153899)
    ·
      refine ⟨402583782200489683344230849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268389188133659788896153899 402583782200489683344230849)
      ·
        refine ⟨301937836650367262508173137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402583782200489683344230849 301937836650367262508173137)
        ·
          refine ⟨226453377487775446881129853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301937836650367262508173137 226453377487775446881129853)
          ·
            refine ⟨84920016557915792580423695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 226453377487775446881129853 84920016557915792580423695)
            ·
              refine ⟨127380024836873688870635543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84920016557915792580423695 127380024836873688870635543)
              ·
                refine ⟨191070037255310533305953315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127380024836873688870635543 191070037255310533305953315)
                ·
                  refine ⟨286605055882965799958929973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191070037255310533305953315 286605055882965799958929973)
                  ·
                    refine ⟨26869223989028043746149685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 286605055882965799958929973 26869223989028043746149685)
                    ·
                      refine ⟨2518989748971379101201533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26869223989028043746149685 2518989748971379101201533)
                      ·
                        rfl

theorem cell23_4905715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 5, 5].length) (baseStart_4905715 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905715 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905715 prefixEnd_4905715 := by exact prefixLift 4905715
  have htrace : WordTrace (prefixWord ++ tailWord_4905715) baseStart_4905715 baseEnd_4905715 := by
    simpa [prefixWord, tailWord_4905715, baseEnd_4905715] using wordTrace_append hprefix tailTrace_4905715
  have hstable : (prefixWord ++ tailWord_4905715).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905715).length < 2 ^ (prefixWord ++ tailWord_4905715).sum := by decide
  have hdescent : baseEnd_4905715 < baseStart_4905715 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905746 : List Nat := [3, 2, 4, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_4905746 : Nat := 118140960795 + 4905746 * 2 ^ 59
def prefixEnd_4905746 : Nat := 4983230072969 + 3 ^ 40 * 4905746 * 2
def baseEnd_4905746 : Nat := 2519005666871668479913891

theorem tailTrace_4905746 : CollatzResearch.WordTrace tailWord_4905746 prefixEnd_4905746 2519005666871668479913891 := by
  unfold tailWord_4905746
  simp only [CollatzResearch.WordTrace]
  refine ⟨44731814021331887889620273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119284837390218367705654061 44731814021331887889620273)
  ·
    refine ⟨33548860515998915917215205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44731814021331887889620273 33548860515998915917215205)
    ·
      refine ⟨6290411346749796734477851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33548860515998915917215205 6290411346749796734477851)
      ·
        refine ⟨9435617020124695101716777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6290411346749796734477851 9435617020124695101716777)
        ·
          refine ⟨7076712765093521326287583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9435617020124695101716777 7076712765093521326287583)
          ·
            refine ⟨10615069147640281989431375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076712765093521326287583 10615069147640281989431375)
            ·
              refine ⟨15922603721460422984147063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615069147640281989431375 15922603721460422984147063)
              ·
                refine ⟨23883905582190634476220595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15922603721460422984147063 23883905582190634476220595)
                ·
                  refine ⟨35825858373285951714330893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23883905582190634476220595 35825858373285951714330893)
                  ·
                    refine ⟨13434696889982231892874085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35825858373285951714330893 13434696889982231892874085)
                    ·
                      refine ⟨2519005666871668479913891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13434696889982231892874085 2519005666871668479913891)
                      ·
                        rfl

theorem cell23_4905746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_4905746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905746 prefixEnd_4905746 := by exact prefixLift 4905746
  have htrace : WordTrace (prefixWord ++ tailWord_4905746) baseStart_4905746 baseEnd_4905746 := by
    simpa [prefixWord, tailWord_4905746, baseEnd_4905746] using wordTrace_append hprefix tailTrace_4905746
  have hstable : (prefixWord ++ tailWord_4905746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905746).length < 2 ^ (prefixWord ++ tailWord_4905746).sum := by decide
  have hdescent : baseEnd_4905746 < baseStart_4905746 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905755 : List Nat := [1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8]
def baseStart_4905755 : Nat := 118140960795 + 4905755 * 2 ^ 59
def prefixEnd_4905755 : Nat := 4983230072969 + 3 ^ 40 * 4905755 * 2
def baseEnd_4905755 : Nat := 2519010288197558944701349

theorem tailTrace_4905755 : CollatzResearch.WordTrace tailWord_4905755 prefixEnd_4905755 2519010288197558944701349 := by
  unfold tailWord_4905755
  simp only [CollatzResearch.WordTrace]
  refine ⟨178927584342294946095558719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119285056228196630730372479 178927584342294946095558719)
  ·
    refine ⟨268391376513442419143338079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178927584342294946095558719 268391376513442419143338079)
    ·
      refine ⟨402587064770163628715007119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268391376513442419143338079 402587064770163628715007119)
      ·
        refine ⟨603880597155245443072510679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402587064770163628715007119 603880597155245443072510679)
        ·
          refine ⟨905820895732868164608766019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603880597155245443072510679 905820895732868164608766019)
          ·
            refine ⟨1358731343599302246913149029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 905820895732868164608766019 1358731343599302246913149029)
            ·
              refine ⟨254762126924869171296215443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1358731343599302246913149029 254762126924869171296215443)
              ·
                refine ⟨382143190387303756944323165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254762126924869171296215443 382143190387303756944323165)
                ·
                  refine ⟨143303696395238908854121187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 382143190387303756944323165 143303696395238908854121187)
                  ·
                    refine ⟨214955544592858363281181781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 143303696395238908854121187 214955544592858363281181781)
                    ·
                      refine ⟨2519010288197558944701349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 214955544592858363281181781 2519010288197558944701349)
                      ·
                        rfl

theorem cell23_4905755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 8].length) (baseStart_4905755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905755 prefixEnd_4905755 := by exact prefixLift 4905755
  have htrace : WordTrace (prefixWord ++ tailWord_4905755) baseStart_4905755 baseEnd_4905755 := by
    simpa [prefixWord, tailWord_4905755, baseEnd_4905755] using wordTrace_append hprefix tailTrace_4905755
  have hstable : (prefixWord ++ tailWord_4905755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905755).length < 2 ^ (prefixWord ++ tailWord_4905755).sum := by decide
  have hdescent : baseEnd_4905755 < baseStart_4905755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905756 : List Nat := [2, 2, 3, 1, 1, 3, 1, 5, 1, 4]
def baseStart_4905756 : Nat := 118140960795 + 4905756 * 2 ^ 59
def prefixEnd_4905756 : Nat := 4983230072969 + 3 ^ 40 * 4905756 * 2
def baseEnd_4905756 : Nat := 839670267226071146929615

theorem tailTrace_4905756 : CollatzResearch.WordTrace tailWord_4905756 prefixEnd_4905756 839670267226071146929615 := by
  unfold tailWord_4905756
  simp only [CollatzResearch.WordTrace]
  refine ⟨89463810407645661633172561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119285080543527548844230081 89463810407645661633172561)
  ·
    refine ⟨67097857805734246224879421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89463810407645661633172561 67097857805734246224879421)
    ·
      refine ⟨25161696677150342334329783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67097857805734246224879421 25161696677150342334329783)
      ·
        refine ⟨37742545015725513501494675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25161696677150342334329783 37742545015725513501494675)
        ·
          refine ⟨56613817523588270252242013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37742545015725513501494675 56613817523588270252242013)
          ·
            refine ⟨21230181571345601344590755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56613817523588270252242013 21230181571345601344590755)
            ·
              refine ⟨31845272357018402016886133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21230181571345601344590755 31845272357018402016886133)
              ·
                refine ⟨2985494283470475189083075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31845272357018402016886133 2985494283470475189083075)
                ·
                  refine ⟨4478241425205712783624613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985494283470475189083075 4478241425205712783624613)
                  ·
                    refine ⟨839670267226071146929615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4478241425205712783624613 839670267226071146929615)
                    ·
                      rfl

theorem cell23_4905756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 5, 1, 4].length) (baseStart_4905756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905756 prefixEnd_4905756 := by exact prefixLift 4905756
  have htrace : WordTrace (prefixWord ++ tailWord_4905756) baseStart_4905756 baseEnd_4905756 := by
    simpa [prefixWord, tailWord_4905756, baseEnd_4905756] using wordTrace_append hprefix tailTrace_4905756
  have hstable : (prefixWord ++ tailWord_4905756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905756).length < 2 ^ (prefixWord ++ tailWord_4905756).sum := by decide
  have hdescent : baseEnd_4905756 < baseStart_4905756 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905786 : List Nat := [3, 1, 1, 1, 6, 1, 3, 1, 6]
def baseStart_4905786 : Nat := 118140960795 + 4905786 * 2 ^ 59
def prefixEnd_4905786 : Nat := 4983230072969 + 3 ^ 40 * 4905786 * 2
def baseEnd_4905786 : Nat := 279891800677538702601523

theorem tailTrace_4905786 : CollatzResearch.WordTrace tailWord_4905786 prefixEnd_4905786 279891800677538702601523 := by
  unfold tailWord_4905786
  simp only [CollatzResearch.WordTrace]
  refine ⟨44732178751295659597484303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119285810003455092259958141 44732178751295659597484303)
  ·
    refine ⟨67098268126943489396226455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44732178751295659597484303 67098268126943489396226455)
    ·
      refine ⟨100647402190415234094339683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67098268126943489396226455 100647402190415234094339683)
      ·
        refine ⟨150971103285622851141509525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100647402190415234094339683 150971103285622851141509525)
        ·
          refine ⟨7076770466513571147258259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 150971103285622851141509525 7076770466513571147258259)
          ·
            refine ⟨10615155699770356720887389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7076770466513571147258259 10615155699770356720887389)
            ·
              refine ⟨3980683387413883770332771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10615155699770356720887389 3980683387413883770332771)
              ·
                refine ⟨5971025081120825655499157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980683387413883770332771 5971025081120825655499157)
                ·
                  refine ⟨279891800677538702601523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5971025081120825655499157 279891800677538702601523)
                  ·
                    rfl

theorem cell23_4905786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 3, 1, 6].length) (baseStart_4905786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905786 prefixEnd_4905786 := by exact prefixLift 4905786
  have htrace : WordTrace (prefixWord ++ tailWord_4905786) baseStart_4905786 baseEnd_4905786 := by
    simpa [prefixWord, tailWord_4905786, baseEnd_4905786] using wordTrace_append hprefix tailTrace_4905786
  have hstable : (prefixWord ++ tailWord_4905786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905786).length < 2 ^ (prefixWord ++ tailWord_4905786).sum := by decide
  have hdescent : baseEnd_4905786 < baseStart_4905786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905829 : List Nat := [1, 3, 1, 3, 1, 1, 4, 1, 4, 4]
def baseStart_4905829 : Nat := 118140960795 + 4905829 * 2 ^ 59
def prefixEnd_4905829 : Nat := 4983230072969 + 3 ^ 40 * 4905829 * 2
def baseEnd_4905829 : Nat := 839682761921997218392003

theorem tailTrace_4905829 : CollatzResearch.WordTrace tailWord_4905829 prefixEnd_4905829 839682761921997218392003 := by
  unfold tailWord_4905829
  simp only [CollatzResearch.WordTrace]
  refine ⟨178930283344026856733752541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119286855562684571155835027 178930283344026856733752541)
  ·
    refine ⟨67098856254010071275157203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178930283344026856733752541 67098856254010071275157203)
    ·
      refine ⟨100648284381015106912735805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67098856254010071275157203 100648284381015106912735805)
      ·
        refine ⟨37743106642880665092275927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100648284381015106912735805 37743106642880665092275927)
        ·
          refine ⟨56614659964320997638413891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37743106642880665092275927 56614659964320997638413891)
          ·
            refine ⟨84921989946481496457620837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56614659964320997638413891 84921989946481496457620837)
            ·
              refine ⟨15922873114965280585803907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84921989946481496457620837 15922873114965280585803907)
              ·
                refine ⟨23884309672447920878705861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15922873114965280585803907 23884309672447920878705861)
                ·
                  refine ⟨4478308063583985164757349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23884309672447920878705861 4478308063583985164757349)
                  ·
                    refine ⟨839682761921997218392003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4478308063583985164757349 839682761921997218392003)
                    ·
                      rfl

theorem cell23_4905829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 1, 4, 4].length) (baseStart_4905829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905829 prefixEnd_4905829 := by exact prefixLift 4905829
  have htrace : WordTrace (prefixWord ++ tailWord_4905829) baseStart_4905829 baseEnd_4905829 := by
    simpa [prefixWord, tailWord_4905829, baseEnd_4905829] using wordTrace_append hprefix tailTrace_4905829
  have hstable : (prefixWord ++ tailWord_4905829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905829).length < 2 ^ (prefixWord ++ tailWord_4905829).sum := by decide
  have hdescent : baseEnd_4905829 < baseStart_4905829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905842 : List Nat := [3, 2, 1, 2, 1, 1, 3, 10]
def baseStart_4905842 : Nat := 118140960795 + 4905842 * 2 ^ 59
def prefixEnd_4905842 : Nat := 4983230072969 + 3 ^ 40 * 4905842 * 2
def baseEnd_4905842 : Nat := 93298331889425929789387

theorem tailTrace_4905842 : CollatzResearch.WordTrace tailWord_4905842 prefixEnd_4905842 93298331889425929789387 := by
  unfold tailWord_4905842
  simp only [CollatzResearch.WordTrace]
  refine ⟨44732689373244939988493945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119287171661986506635983853 44732689373244939988493945)
  ·
    refine ⟨33549517029933704991370459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44732689373244939988493945 33549517029933704991370459)
    ·
      refine ⟨50324275544900557487055689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33549517029933704991370459 50324275544900557487055689)
      ·
        refine ⟨37743206658675418115291767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50324275544900557487055689 37743206658675418115291767)
        ·
          refine ⟨56614809988013127172937651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37743206658675418115291767 56614809988013127172937651)
          ·
            refine ⟨84922214982019690759406477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56614809988013127172937651 84922214982019690759406477)
            ·
              refine ⟨31845830618257384034777429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84922214982019690759406477 31845830618257384034777429)
              ·
                refine ⟨93298331889425929789387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31845830618257384034777429 93298331889425929789387)
                ·
                  rfl

theorem cell23_4905842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 10].length) (baseStart_4905842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905842 prefixEnd_4905842 := by exact prefixLift 4905842
  have htrace : WordTrace (prefixWord ++ tailWord_4905842) baseStart_4905842 baseEnd_4905842 := by
    simpa [prefixWord, tailWord_4905842, baseEnd_4905842] using wordTrace_append hprefix tailTrace_4905842
  have hstable : (prefixWord ++ tailWord_4905842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905842).length < 2 ^ (prefixWord ++ tailWord_4905842).sum := by decide
  have hdescent : baseEnd_4905842 < baseStart_4905842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905866 : List Nat := [3, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_4905866 : Nat := 118140960795 + 4905866 * 2 ^ 59
def prefixEnd_4905866 : Nat := 4983230072969 + 3 ^ 40 * 4905866 * 2
def baseEnd_4905866 : Nat := 2519067284550208010413339

theorem tailTrace_4905866 : CollatzResearch.WordTrace tailWord_4905866 prefixEnd_4905866 2519067284550208010413339 := by
  unfold tailWord_4905866
  simp only [CollatzResearch.WordTrace]
  refine ⟨44732908211223203013212363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119287755229928541368566301 44732908211223203013212363)
  ·
    refine ⟨67099362316834804519818545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44732908211223203013212363 67099362316834804519818545)
    ·
      refine ⟨50324521737626103389863909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67099362316834804519818545 50324521737626103389863909)
      ·
        refine ⟨9435847825804894385599483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50324521737626103389863909 9435847825804894385599483)
        ·
          refine ⟨14153771738707341578399225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435847825804894385599483 14153771738707341578399225)
          ·
            refine ⟨10615328804030506183799419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14153771738707341578399225 10615328804030506183799419)
            ·
              refine ⟨15922993206045759275699129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615328804030506183799419 15922993206045759275699129)
              ·
                refine ⟨11942244904534319456774347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15922993206045759275699129 11942244904534319456774347)
                ·
                  refine ⟨17913367356801479185161521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11942244904534319456774347 17913367356801479185161521)
                  ·
                    refine ⟨13435025517601109388871141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17913367356801479185161521 13435025517601109388871141)
                    ·
                      refine ⟨2519067284550208010413339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13435025517601109388871141 2519067284550208010413339)
                      ·
                        rfl

theorem cell23_4905866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_4905866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905866 prefixEnd_4905866 := by exact prefixLift 4905866
  have htrace : WordTrace (prefixWord ++ tailWord_4905866) baseStart_4905866 baseEnd_4905866 := by
    simpa [prefixWord, tailWord_4905866, baseEnd_4905866] using wordTrace_append hprefix tailTrace_4905866
  have hstable : (prefixWord ++ tailWord_4905866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905866).length < 2 ^ (prefixWord ++ tailWord_4905866).sum := by decide
  have hdescent : baseEnd_4905866 < baseStart_4905866 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905887 : List Nat := [1, 1, 2, 5, 2, 1, 4, 2, 1, 2, 2]
def baseStart_4905887 : Nat := 118140960795 + 4905887 * 2 ^ 59
def prefixEnd_4905887 : Nat := 4983230072969 + 3 ^ 40 * 4905887 * 2
def baseEnd_4905887 : Nat := 2519078067643952428250743

theorem tailTrace_4905887 : CollatzResearch.WordTrace tailWord_4905887 prefixEnd_4905887 2519078067643952428250743 := by
  unfold tailWord_4905887
  simp only [CollatzResearch.WordTrace]
  refine ⟨178932398777816732639363915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119288265851877821759575943 178932398777816732639363915)
  ·
    refine ⟨268398598166725098959045873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178932398777816732639363915 268398598166725098959045873)
    ·
      refine ⟨201298948625043824219284405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268398598166725098959045873 201298948625043824219284405)
      ·
        refine ⟨18871776433597858520557913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201298948625043824219284405 18871776433597858520557913)
        ·
          refine ⟨14153832325198393890418435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18871776433597858520557913 14153832325198393890418435)
          ·
            refine ⟨21230748487797590835627653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14153832325198393890418435 21230748487797590835627653)
            ·
              refine ⟨3980765341462048281680185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21230748487797590835627653 3980765341462048281680185)
              ·
                refine ⟨2985574006096536211260139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3980765341462048281680185 2985574006096536211260139)
                ·
                  refine ⟨4478361009144804316890209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2985574006096536211260139 4478361009144804316890209)
                  ·
                    refine ⟨3358770756858603237667657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478361009144804316890209 3358770756858603237667657)
                    ·
                      refine ⟨2519078067643952428250743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358770756858603237667657 2519078067643952428250743)
                      ·
                        rfl

theorem cell23_4905887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 4, 2, 1, 2, 2].length) (baseStart_4905887 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905887 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905887 prefixEnd_4905887 := by exact prefixLift 4905887
  have htrace : WordTrace (prefixWord ++ tailWord_4905887) baseStart_4905887 baseEnd_4905887 := by
    simpa [prefixWord, tailWord_4905887, baseEnd_4905887] using wordTrace_append hprefix tailTrace_4905887
  have hstable : (prefixWord ++ tailWord_4905887).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905887).length < 2 ^ (prefixWord ++ tailWord_4905887).sum := by decide
  have hdescent : baseEnd_4905887 < baseStart_4905887 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905889 : List Nat := [1, 2, 3, 4, 1, 1, 1, 1, 2, 7]
def baseStart_4905889 : Nat := 118140960795 + 4905889 * 2 ^ 59
def prefixEnd_4905889 : Nat := 4983230072969 + 3 ^ 40 * 4905889 * 2
def baseEnd_4905889 : Nat := 839693031535087140141911

theorem tailTrace_4905889 : CollatzResearch.WordTrace tailWord_4905889 prefixEnd_4905889 839693031535087140141911 := by
  unfold tailWord_4905889
  simp only [CollatzResearch.WordTrace]
  refine ⟨178932471723809486980936721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119288314482539657987291147 178932471723809486980936721)
  ·
    refine ⟨134199353792857115235702541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178932471723809486980936721 134199353792857115235702541)
    ·
      refine ⟨50324757672321418213388453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134199353792857115235702541 50324757672321418213388453)
      ·
        refine ⟨9435892063560265915010335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50324757672321418213388453 9435892063560265915010335)
        ·
          refine ⟨14153838095340398872515503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9435892063560265915010335 14153838095340398872515503)
          ·
            refine ⟨21230757143010598308773255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14153838095340398872515503 21230757143010598308773255)
            ·
              refine ⟨31846135714515897463159883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21230757143010598308773255 31846135714515897463159883)
              ·
                refine ⟨47769203571773846194739825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31846135714515897463159883 47769203571773846194739825)
                ·
                  refine ⟨35826902678830384646054869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47769203571773846194739825 35826902678830384646054869)
                  ·
                    refine ⟨839693031535087140141911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35826902678830384646054869 839693031535087140141911)
                    ·
                      rfl

theorem cell23_4905889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 2, 7].length) (baseStart_4905889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905889 prefixEnd_4905889 := by exact prefixLift 4905889
  have htrace : WordTrace (prefixWord ++ tailWord_4905889) baseStart_4905889 baseEnd_4905889 := by
    simpa [prefixWord, tailWord_4905889, baseEnd_4905889] using wordTrace_append hprefix tailTrace_4905889
  have hstable : (prefixWord ++ tailWord_4905889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905889).length < 2 ^ (prefixWord ++ tailWord_4905889).sum := by decide
  have hdescent : baseEnd_4905889 < baseStart_4905889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905909 : List Nat := [1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 4]
def baseStart_4905909 : Nat := 118140960795 + 4905909 * 2 ^ 59
def prefixEnd_4905909 : Nat := 4983230072969 + 3 ^ 40 * 4905909 * 2
def baseEnd_4905909 : Nat := 2519089364218351342175641

theorem tailTrace_4905909 : CollatzResearch.WordTrace tailWord_4905909 prefixEnd_4905909 2519089364218351342175641 := by
  unfold tailWord_4905909
  simp only [CollatzResearch.WordTrace]
  refine ⟨178933201183737030396664781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119288800789158020264443187 178933201183737030396664781)
  ·
    refine ⟨67099950443901386398749293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178933201183737030396664781 67099950443901386398749293)
    ·
      refine ⟨25162481416463019899530985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67099950443901386398749293 25162481416463019899530985)
      ·
        refine ⟨18871861062347264924648239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25162481416463019899530985 18871861062347264924648239)
        ·
          refine ⟨28307791593520897386972359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18871861062347264924648239 28307791593520897386972359)
          ·
            refine ⟨42461687390281346080458539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28307791593520897386972359 42461687390281346080458539)
            ·
              refine ⟨63692531085422019120687809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42461687390281346080458539 63692531085422019120687809)
              ·
                refine ⟨47769398314066514340515857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63692531085422019120687809 47769398314066514340515857)
                ·
                  refine ⟨35827048735549885755386893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47769398314066514340515857 35827048735549885755386893)
                  ·
                    refine ⟨13435143275831207158270085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35827048735549885755386893 13435143275831207158270085)
                    ·
                      refine ⟨2519089364218351342175641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13435143275831207158270085 2519089364218351342175641)
                      ·
                        rfl

theorem cell23_4905909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 2, 2, 3, 4].length) (baseStart_4905909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905909 prefixEnd_4905909 := by exact prefixLift 4905909
  have htrace : WordTrace (prefixWord ++ tailWord_4905909) baseStart_4905909 baseEnd_4905909 := by
    simpa [prefixWord, tailWord_4905909, baseEnd_4905909] using wordTrace_append hprefix tailTrace_4905909
  have hstable : (prefixWord ++ tailWord_4905909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905909).length < 2 ^ (prefixWord ++ tailWord_4905909).sum := by decide
  have hdescent : baseEnd_4905909 < baseStart_4905909 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905924 : List Nat := [2, 3, 3, 3, 2, 1, 2, 1, 1, 2, 3]
def baseStart_4905924 : Nat := 118140960795 + 4905924 * 2 ^ 59
def prefixEnd_4905924 : Nat := 4983230072969 + 3 ^ 40 * 4905924 * 2
def baseEnd_4905924 : Nat := 2519097066428168783488073

theorem tailTrace_4905924 : CollatzResearch.WordTrace tailWord_4905924 prefixEnd_4905924 2519097066428168783488073 := by
  unfold tailWord_4905924
  simp only [CollatzResearch.WordTrace]
  refine ⟨89466874139341343979230413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119289165519121791972307217 89466874139341343979230413)
  ·
    refine ⟨33550077802253003992211405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89466874139341343979230413 33550077802253003992211405)
    ·
      refine ⟨12581279175844876497079277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33550077802253003992211405 12581279175844876497079277)
      ·
        refine ⟨4717979690941828686404729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12581279175844876497079277 4717979690941828686404729)
        ·
          refine ⟨3538484768206371514803547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4717979690941828686404729 3538484768206371514803547)
          ·
            refine ⟨5307727152309557272205321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3538484768206371514803547 5307727152309557272205321)
            ·
              refine ⟨3980795364232167954153991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5307727152309557272205321 3980795364232167954153991)
              ·
                refine ⟨5971193046348251931230987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3980795364232167954153991 5971193046348251931230987)
                ·
                  refine ⟨8956789569522377896846481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5971193046348251931230987 8956789569522377896846481)
                  ·
                    refine ⟨6717592177141783422634861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8956789569522377896846481 6717592177141783422634861)
                    ·
                      refine ⟨2519097066428168783488073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6717592177141783422634861 2519097066428168783488073)
                      ·
                        rfl

theorem cell23_4905924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_4905924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905924 prefixEnd_4905924 := by exact prefixLift 4905924
  have htrace : WordTrace (prefixWord ++ tailWord_4905924) baseStart_4905924 baseEnd_4905924 := by
    simpa [prefixWord, tailWord_4905924, baseEnd_4905924] using wordTrace_append hprefix tailTrace_4905924
  have hstable : (prefixWord ++ tailWord_4905924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905924).length < 2 ^ (prefixWord ++ tailWord_4905924).sum := by decide
  have hdescent : baseEnd_4905924 < baseStart_4905924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905943 : List Nat := [1, 1, 3, 2, 1, 1, 2, 6, 2, 2, 2]
def baseStart_4905943 : Nat := 118140960795 + 4905943 * 2 ^ 59
def prefixEnd_4905943 : Nat := 4983230072969 + 3 ^ 40 * 4905943 * 2
def baseEnd_4905943 : Nat := 2519106822560604209150485

theorem tailTrace_4905943 : CollatzResearch.WordTrace tailWord_4905943 prefixEnd_4905943 2519106822560604209150485 := by
  unfold tailWord_4905943
  simp only [CollatzResearch.WordTrace]
  refine ⟨178934441265613854203402483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119289627510409236135601655 178934441265613854203402483)
  ·
    refine ⟨268401661898420781305103725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178934441265613854203402483 268401661898420781305103725)
    ·
      refine ⟨100650623211907792989413897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268401661898420781305103725 100650623211907792989413897)
      ·
        refine ⟨75487967408930844742060423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100650623211907792989413897 75487967408930844742060423)
        ·
          refine ⟨113231951113396267113090635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75487967408930844742060423 113231951113396267113090635)
          ·
            refine ⟨169847926670094400669635953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113231951113396267113090635 169847926670094400669635953)
            ·
              refine ⟨127385945002570800502226965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169847926670094400669635953 127385945002570800502226965)
              ·
                refine ⟨5971216171995506273541889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127385945002570800502226965 5971216171995506273541889)
                ·
                  refine ⟨4478412128996629705156417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5971216171995506273541889 4478412128996629705156417)
                  ·
                    refine ⟨3358809096747472278867313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478412128996629705156417 3358809096747472278867313)
                    ·
                      refine ⟨2519106822560604209150485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358809096747472278867313 2519106822560604209150485)
                      ·
                        rfl

theorem cell23_4905943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 2, 6, 2, 2, 2].length) (baseStart_4905943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905943 prefixEnd_4905943 := by exact prefixLift 4905943
  have htrace : WordTrace (prefixWord ++ tailWord_4905943) baseStart_4905943 baseEnd_4905943 := by
    simpa [prefixWord, tailWord_4905943, baseEnd_4905943] using wordTrace_append hprefix tailTrace_4905943
  have hstable : (prefixWord ++ tailWord_4905943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905943).length < 2 ^ (prefixWord ++ tailWord_4905943).sum := by decide
  have hdescent : baseEnd_4905943 < baseStart_4905943 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905979 : List Nat := [1, 1, 1, 1, 1, 3, 3, 5, 2, 5]
def baseStart_4905979 : Nat := 118140960795 + 4905979 * 2 ^ 59
def prefixEnd_4905979 : Nat := 4983230072969 + 3 ^ 40 * 4905979 * 2
def baseEnd_4905979 : Nat := 839708435954722022766773

theorem tailTrace_4905979 : CollatzResearch.WordTrace tailWord_4905979 prefixEnd_4905979 839708435954722022766773 := by
  unfold tailWord_4905979
  simp only [CollatzResearch.WordTrace]
  refine ⟨178935754293483432351712991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119290502862322288234475327 178935754293483432351712991)
  ·
    refine ⟨268403631440225148527569487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178935754293483432351712991 268403631440225148527569487)
    ·
      refine ⟨402605447160337722791354231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268403631440225148527569487 402605447160337722791354231)
      ·
        refine ⟨603908170740506584187031347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402605447160337722791354231 603908170740506584187031347)
        ·
          refine ⟨905862256110759876280547021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 603908170740506584187031347 905862256110759876280547021)
          ·
            refine ⟨339698346041534953605205133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 905862256110759876280547021 339698346041534953605205133)
            ·
              refine ⟨127386879765575607601951925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339698346041534953605205133 127386879765575607601951925)
              ·
                refine ⟨11942519978022713212682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127386879765575607601951925 11942519978022713212682993)
                ·
                  refine ⟨8956889983517034909512245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11942519978022713212682993 8956889983517034909512245)
                  ·
                    refine ⟨839708435954722022766773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8956889983517034909512245 839708435954722022766773)
                    ·
                      rfl

theorem cell23_4905979_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 5, 2, 5].length) (baseStart_4905979 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905979 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905979 prefixEnd_4905979 := by exact prefixLift 4905979
  have htrace : WordTrace (prefixWord ++ tailWord_4905979) baseStart_4905979 baseEnd_4905979 := by
    simpa [prefixWord, tailWord_4905979, baseEnd_4905979] using wordTrace_append hprefix tailTrace_4905979
  have hstable : (prefixWord ++ tailWord_4905979).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905979).length < 2 ^ (prefixWord ++ tailWord_4905979).sum := by decide
  have hdescent : baseEnd_4905979 < baseStart_4905979 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905979) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905989 : List Nat := [1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 5]
def baseStart_4905989 : Nat := 118140960795 + 4905989 * 2 ^ 59
def prefixEnd_4905989 : Nat := 4983230072969 + 3 ^ 40 * 4905989 * 2
def baseEnd_4905989 : Nat := 2519130442670711029175273

theorem tailTrace_4905989 : CollatzResearch.WordTrace tailWord_4905989 prefixEnd_4905989 2519130442670711029175273 := by
  unfold tailWord_4905989
  simp only [CollatzResearch.WordTrace]
  refine ⟨178936119023447204059577021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119290746015631469373051347 178936119023447204059577021)
  ·
    refine ⟨67101044633792701522341383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178936119023447204059577021 67101044633792701522341383)
    ·
      refine ⟨100651566950689052283512075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67101044633792701522341383 100651566950689052283512075)
      ·
        refine ⟨150977350426033578425268113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100651566950689052283512075 150977350426033578425268113)
        ·
          refine ⟨113233012819525183818951085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150977350426033578425268113 113233012819525183818951085)
          ·
            refine ⟨42462379807321943932106657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113233012819525183818951085 42462379807321943932106657)
            ·
              refine ⟨31846784855491457949079993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42462379807321943932106657 31846784855491457949079993)
              ·
                refine ⟨23885088641618593461809995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31846784855491457949079993 23885088641618593461809995)
                ·
                  refine ⟨35827632962427890192714993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23885088641618593461809995 35827632962427890192714993)
                  ·
                    refine ⟨26870724721820917644536245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35827632962427890192714993 26870724721820917644536245)
                    ·
                      refine ⟨2519130442670711029175273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26870724721820917644536245 2519130442670711029175273)
                      ·
                        rfl

theorem cell23_4905989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 2, 1, 2, 5].length) (baseStart_4905989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905989 prefixEnd_4905989 := by exact prefixLift 4905989
  have htrace : WordTrace (prefixWord ++ tailWord_4905989) baseStart_4905989 baseEnd_4905989 := by
    simpa [prefixWord, tailWord_4905989, baseEnd_4905989] using wordTrace_append hprefix tailTrace_4905989
  have hstable : (prefixWord ++ tailWord_4905989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905989).length < 2 ^ (prefixWord ++ tailWord_4905989).sum := by decide
  have hdescent : baseEnd_4905989 < baseStart_4905989 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4905996 : List Nat := [2, 2, 1, 2, 3, 3, 1, 2, 2, 5]
def baseStart_4905996 : Nat := 118140960795 + 4905996 * 2 ^ 59
def prefixEnd_4905996 : Nat := 4983230072969 + 3 ^ 40 * 4905996 * 2
def baseEnd_4905996 : Nat := 839711345678430833929247

theorem tailTrace_4905996 : CollatzResearch.WordTrace tailWord_4905996 prefixEnd_4905996 839711345678430833929247 := by
  unfold tailWord_4905996
  simp only [CollatzResearch.WordTrace]
  refine ⟨89468187167210922127540921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119290916222947896170054561 89468187167210922127540921)
  ·
    refine ⟨67101140375408191595655691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89468187167210922127540921 67101140375408191595655691)
    ·
      refine ⟨100651710563112287393483537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67101140375408191595655691 100651710563112287393483537)
      ·
        refine ⟨75488782922334215545112653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100651710563112287393483537 75488782922334215545112653)
        ·
          refine ⟨28308293595875330829417245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75488782922334215545112653 28308293595875330829417245)
          ·
            refine ⟨10615610098453249061031467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28308293595875330829417245 10615610098453249061031467)
            ·
              refine ⟨15923415147679873591547201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10615610098453249061031467 15923415147679873591547201)
              ·
                refine ⟨11942561360759905193660401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15923415147679873591547201 11942561360759905193660401)
                ·
                  refine ⟨8956921020569928895245301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11942561360759905193660401 8956921020569928895245301)
                  ·
                    refine ⟨839711345678430833929247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8956921020569928895245301 839711345678430833929247)
                    ·
                      rfl

theorem cell23_4905996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 2, 2, 5].length) (baseStart_4905996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4905996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4905996 prefixEnd_4905996 := by exact prefixLift 4905996
  have htrace : WordTrace (prefixWord ++ tailWord_4905996) baseStart_4905996 baseEnd_4905996 := by
    simpa [prefixWord, tailWord_4905996, baseEnd_4905996] using wordTrace_append hprefix tailTrace_4905996
  have hstable : (prefixWord ++ tailWord_4905996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4905996).length < 2 ^ (prefixWord ++ tailWord_4905996).sum := by decide
  have hdescent : baseEnd_4905996 < baseStart_4905996 := by decide
  rcases family_descends (prefixWord ++ tailWord_4905996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906056 : List Nat := [2, 1, 3, 1, 1, 1, 6, 2, 6]
def baseStart_4906056 : Nat := 118140960795 + 4906056 * 2 ^ 59
def prefixEnd_4906056 : Nat := 4983230072969 + 3 ^ 40 * 4906056 * 2
def baseEnd_4906056 : Nat := 279907205097173585226385

theorem tailTrace_4906056 : CollatzResearch.WordTrace tailWord_4906056 prefixEnd_4906056 279907205097173585226385 := by
  unfold tailWord_4906056
  simp only [CollatzResearch.WordTrace]
  refine ⟨89469281357102237251133011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119292375142802983001510681 89469281357102237251133011)
  ·
    refine ⟨134203922035653355876699517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89469281357102237251133011 134203922035653355876699517)
    ·
      refine ⟨50326470763370008453762319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134203922035653355876699517 50326470763370008453762319)
      ·
        refine ⟨75489706145055012680643479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50326470763370008453762319 75489706145055012680643479)
        ·
          refine ⟨113234559217582519020965219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75489706145055012680643479 113234559217582519020965219)
          ·
            refine ⟨169851838826373778531447829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113234559217582519020965219 169851838826373778531447829)
            ·
              refine ⟨7961804944986270868661617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 169851838826373778531447829 7961804944986270868661617)
              ·
                refine ⟨5971353708739703151496213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7961804944986270868661617 5971353708739703151496213)
                ·
                  refine ⟨279907205097173585226385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5971353708739703151496213 279907205097173585226385)
                  ·
                    rfl

theorem cell23_4906056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 6, 2, 6].length) (baseStart_4906056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906056 prefixEnd_4906056 := by exact prefixLift 4906056
  have htrace : WordTrace (prefixWord ++ tailWord_4906056) baseStart_4906056 baseEnd_4906056 := by
    simpa [prefixWord, tailWord_4906056, baseEnd_4906056] using wordTrace_append hprefix tailTrace_4906056
  have hstable : (prefixWord ++ tailWord_4906056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906056).length < 2 ^ (prefixWord ++ tailWord_4906056).sum := by decide
  have hdescent : baseEnd_4906056 < baseStart_4906056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906079 : List Nat := [1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7]
def baseStart_4906079 : Nat := 118140960795 + 4906079 * 2 ^ 59
def prefixEnd_4906079 : Nat := 4983230072969 + 3 ^ 40 * 4906079 * 2
def baseEnd_4906079 : Nat := 2519176655929615677049859

theorem tailTrace_4906079 : CollatzResearch.WordTrace tailWord_4906079 prefixEnd_4906079 2519176655929615677049859 := by
  unfold tailWord_4906079
  simp only [CollatzResearch.WordTrace]
  refine ⟨178939401593121149430353291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119292934395414099620235527 178939401593121149430353291)
  ·
    refine ⟨268409102389681724145529937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178939401593121149430353291 268409102389681724145529937)
    ·
      refine ⟨201306826792261293109147453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268409102389681724145529937 201306826792261293109147453)
      ·
        refine ⟨75490060047097984915930295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201306826792261293109147453 75490060047097984915930295)
        ·
          refine ⟨113235090070646977373895443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75490060047097984915930295 113235090070646977373895443)
          ·
            refine ⟨169852635105970466060843165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113235090070646977373895443 169852635105970466060843165)
            ·
              refine ⟨63694738164738924772816187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169852635105970466060843165 63694738164738924772816187)
              ·
                refine ⟨95542107247108387159224281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63694738164738924772816187 95542107247108387159224281)
                ·
                  refine ⟨71656580435331290369418211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95542107247108387159224281 71656580435331290369418211)
                  ·
                    refine ⟨107484870652996935554127317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71656580435331290369418211 107484870652996935554127317)
                    ·
                      refine ⟨2519176655929615677049859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107484870652996935554127317 2519176655929615677049859)
                      ·
                        rfl

theorem cell23_4906079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_4906079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906079 prefixEnd_4906079 := by exact prefixLift 4906079
  have htrace : WordTrace (prefixWord ++ tailWord_4906079) baseStart_4906079 baseEnd_4906079 := by
    simpa [prefixWord, tailWord_4906079, baseEnd_4906079] using wordTrace_append hprefix tailTrace_4906079
  have hstable : (prefixWord ++ tailWord_4906079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906079).length < 2 ^ (prefixWord ++ tailWord_4906079).sum := by decide
  have hdescent : baseEnd_4906079 < baseStart_4906079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906140 : List Nat := [2, 2, 3, 2, 1, 3, 2, 2, 1, 1, 4]
def baseStart_4906140 : Nat := 118140960795 + 4906140 * 2 ^ 59
def prefixEnd_4906140 : Nat := 4983230072969 + 3 ^ 40 * 4906140 * 2
def baseEnd_4906140 : Nat := 2519207978249539938387079

theorem tailTrace_4906140 : CollatzResearch.WordTrace tailWord_4906140 prefixEnd_4906140 2519207978249539938387079 := by
  unfold tailWord_4906140
  simp only [CollatzResearch.WordTrace]
  refine ⟨89470813222950078424161937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119294417630600104565549249 89470813222950078424161937)
  ·
    refine ⟨67103109917212558818121453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89470813222950078424161937 67103109917212558818121453)
    ·
      refine ⟨25163666218954709556795545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67103109917212558818121453 25163666218954709556795545)
      ·
        refine ⟨18872749664216032167596659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25163666218954709556795545 18872749664216032167596659)
        ·
          refine ⟨28309124496324048251394989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18872749664216032167596659 28309124496324048251394989)
          ·
            refine ⟨10615921686121518094273121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28309124496324048251394989 10615921686121518094273121)
            ·
              refine ⟨7961941264591138570704841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10615921686121518094273121 7961941264591138570704841)
              ·
                refine ⟨5971455948443353928028631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7961941264591138570704841 5971455948443353928028631)
                ·
                  refine ⟨8957183922665030892042947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5971455948443353928028631 8957183922665030892042947)
                  ·
                    refine ⟨13435775883997546338064421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8957183922665030892042947 13435775883997546338064421)
                    ·
                      refine ⟨2519207978249539938387079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13435775883997546338064421 2519207978249539938387079)
                      ·
                        rfl

theorem cell23_4906140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_4906140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906140 prefixEnd_4906140 := by exact prefixLift 4906140
  have htrace : WordTrace (prefixWord ++ tailWord_4906140) baseStart_4906140 baseEnd_4906140 := by
    simpa [prefixWord, tailWord_4906140, baseEnd_4906140] using wordTrace_append hprefix tailTrace_4906140
  have hstable : (prefixWord ++ tailWord_4906140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906140).length < 2 ^ (prefixWord ++ tailWord_4906140).sum := by decide
  have hdescent : baseEnd_4906140 < baseStart_4906140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906174 : List Nat := [4, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_4906174 : Nat := 118140960795 + 4906174 * 2 ^ 59
def prefixEnd_4906174 : Nat := 4983230072969 + 3 ^ 40 * 4906174 * 2
def baseEnd_4906174 : Nat := 2519225436591792805361923

theorem tailTrace_4906174 : CollatzResearch.WordTrace tailWord_4906174 prefixEnd_4906174 2519225436591792805361923 := by
  unfold tailWord_4906174
  simp only [CollatzResearch.WordTrace]
  refine ⟨22367858315972122581882697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119295244351851320436707717 22367858315972122581882697)
  ·
    refine ⟨16775893736979091936412023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22367858315972122581882697 16775893736979091936412023)
    ·
      refine ⟨25163840605468637904618035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16775893736979091936412023 25163840605468637904618035)
      ·
        refine ⟨37745760908202956856927053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25163840605468637904618035 37745760908202956856927053)
        ·
          refine ⟨14154660340576108821347645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37745760908202956856927053 14154660340576108821347645)
          ·
            refine ⟨5307997627716040808005367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14154660340576108821347645 5307997627716040808005367)
            ·
              refine ⟨7961996441574061212008051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5307997627716040808005367 7961996441574061212008051)
              ·
                refine ⟨11942994662361091818012077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7961996441574061212008051 11942994662361091818012077)
                ·
                  refine ⟨4478622998385409431754529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11942994662361091818012077 4478622998385409431754529)
                  ·
                    refine ⟨3358967248789057073815897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478622998385409431754529 3358967248789057073815897)
                    ·
                      refine ⟨2519225436591792805361923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3358967248789057073815897 2519225436591792805361923)
                      ·
                        rfl

theorem cell23_4906174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_4906174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906174 prefixEnd_4906174 := by exact prefixLift 4906174
  have htrace : WordTrace (prefixWord ++ tailWord_4906174) baseStart_4906174 baseEnd_4906174 := by
    simpa [prefixWord, tailWord_4906174, baseEnd_4906174] using wordTrace_append hprefix tailTrace_4906174
  have hstable : (prefixWord ++ tailWord_4906174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906174).length < 2 ^ (prefixWord ++ tailWord_4906174).sum := by decide
  have hdescent : baseEnd_4906174 < baseStart_4906174 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906230 : List Nat := [5, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2]
def baseStart_4906230 : Nat := 118140960795 + 4906230 * 2 ^ 59
def prefixEnd_4906230 : Nat := 4983230072969 + 3 ^ 40 * 4906230 * 2
def baseEnd_4906230 : Nat := 2519254191508444586261665

theorem tailTrace_4906230 : CollatzResearch.WordTrace tailWord_4906230 prefixEnd_4906230 2519254191508444586261665 := by
  unfold tailWord_4906230
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184056813473381388693759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119296606010382734812733429 11184056813473381388693759)
  ·
    refine ⟨16776085220210072083040639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11184056813473381388693759 16776085220210072083040639)
    ·
      refine ⟨25164127830315108124560959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16776085220210072083040639 25164127830315108124560959)
      ·
        refine ⟨37746191745472662186841439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25164127830315108124560959 37746191745472662186841439)
        ·
          refine ⟨56619287618208993280262159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37746191745472662186841439 56619287618208993280262159)
          ·
            refine ⟨84928931427313489920393239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56619287618208993280262159 84928931427313489920393239)
            ·
              refine ⟨127393397140970234880589859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84928931427313489920393239 127393397140970234880589859)
              ·
                refine ⟨191090095711455352320884789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127393397140970234880589859 191090095711455352320884789)
                ·
                  refine ⟨17914696472948939280082949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 191090095711455352320884789 17914696472948939280082949)
                  ·
                    refine ⟨3359005588677926115015553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17914696472948939280082949 3359005588677926115015553)
                    ·
                      refine ⟨2519254191508444586261665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359005588677926115015553 2519254191508444586261665)
                      ·
                        rfl

theorem cell23_4906230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 1, 1, 5, 4, 2].length) (baseStart_4906230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906230 prefixEnd_4906230 := by exact prefixLift 4906230
  have htrace : WordTrace (prefixWord ++ tailWord_4906230) baseStart_4906230 baseEnd_4906230 := by
    simpa [prefixWord, tailWord_4906230, baseEnd_4906230] using wordTrace_append hprefix tailTrace_4906230
  have hstable : (prefixWord ++ tailWord_4906230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906230).length < 2 ^ (prefixWord ++ tailWord_4906230).sum := by decide
  have hdescent : baseEnd_4906230 < baseStart_4906230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906243 : List Nat := [1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4]
def baseStart_4906243 : Nat := 118140960795 + 4906243 * 2 ^ 59
def prefixEnd_4906243 : Nat := 4983230072969 + 3 ^ 40 * 4906243 * 2
def baseEnd_4906243 : Nat := 2519260866756953035399105

theorem tailTrace_4906243 : CollatzResearch.WordTrace tailWord_4906243 prefixEnd_4906243 2519260866756953035399105 := by
  unfold tailWord_4906243
  simp only [CollatzResearch.WordTrace]
  refine ⟨178945383164527005439323383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119296922109684670292882255 178945383164527005439323383)
  ·
    refine ⟨268418074746790508158985075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178945383164527005439323383 268418074746790508158985075)
    ·
      refine ⟨402627112120185762238477613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268418074746790508158985075 402627112120185762238477613)
      ·
        refine ⟨150985167045069660839429105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402627112120185762238477613 150985167045069660839429105)
        ·
          refine ⟨113238875283802245629571829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 150985167045069660839429105 113238875283802245629571829)
          ·
            refine ⟨10616144557856460527772359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113238875283802245629571829 10616144557856460527772359)
            ·
              refine ⟨15924216836784690791658539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10616144557856460527772359 15924216836784690791658539)
              ·
                refine ⟨23886325255177036187487809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15924216836784690791658539 23886325255177036187487809)
                ·
                  refine ⟨17914743941382777140615857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23886325255177036187487809 17914743941382777140615857)
                  ·
                    refine ⟨13436057956037082855461893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17914743941382777140615857 13436057956037082855461893)
                    ·
                      refine ⟨2519260866756953035399105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13436057956037082855461893 2519260866756953035399105)
                      ·
                        rfl

theorem cell23_4906243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 1, 2, 2, 4].length) (baseStart_4906243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906243 prefixEnd_4906243 := by exact prefixLift 4906243
  have htrace : WordTrace (prefixWord ++ tailWord_4906243) baseStart_4906243 baseEnd_4906243 := by
    simpa [prefixWord, tailWord_4906243, baseEnd_4906243] using wordTrace_append hprefix tailTrace_4906243
  have hstable : (prefixWord ++ tailWord_4906243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906243).length < 2 ^ (prefixWord ++ tailWord_4906243).sum := by decide
  have hdescent : baseEnd_4906243 < baseStart_4906243 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906263 : List Nat := [1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3]
def baseStart_4906263 : Nat := 118140960795 + 4906263 * 2 ^ 59
def prefixEnd_4906263 : Nat := 4983230072969 + 3 ^ 40 * 4906263 * 2
def baseEnd_4906263 : Nat := 2519271136370042957149013

theorem tailTrace_4906263 : CollatzResearch.WordTrace tailWord_4906263 prefixEnd_4906263 2519271136370042957149013 := by
  unfold tailWord_4906263
  simp only [CollatzResearch.WordTrace]
  refine ⟨178946112624454548855051443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119297408416303032570034295 178946112624454548855051443)
  ·
    refine ⟨268419168936681823282577165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178946112624454548855051443 268419168936681823282577165)
    ·
      refine ⟨100657188351255683730966437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268419168936681823282577165 100657188351255683730966437)
      ·
        refine ⟨18873222815860440699556207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100657188351255683730966437 18873222815860440699556207)
        ·
          refine ⟨28309834223790661049334311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18873222815860440699556207 28309834223790661049334311)
          ·
            refine ⟨42464751335685991574001467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28309834223790661049334311 42464751335685991574001467)
            ·
              refine ⟨63697127003528987361002201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42464751335685991574001467 63697127003528987361002201)
              ·
                refine ⟨47772845252646740520751651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63697127003528987361002201 47772845252646740520751651)
                ·
                  refine ⟨71659267878970110781127477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47772845252646740520751651 71659267878970110781127477)
                  ·
                    refine ⟨6718056363653447885730701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71659267878970110781127477 6718056363653447885730701)
                    ·
                      refine ⟨2519271136370042957149013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718056363653447885730701 2519271136370042957149013)
                      ·
                        rfl

theorem cell23_4906263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_4906263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906263 prefixEnd_4906263 := by exact prefixLift 4906263
  have htrace : WordTrace (prefixWord ++ tailWord_4906263) baseStart_4906263 baseEnd_4906263 := by
    simpa [prefixWord, tailWord_4906263, baseEnd_4906263] using wordTrace_append hprefix tailTrace_4906263
  have hstable : (prefixWord ++ tailWord_4906263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906263).length < 2 ^ (prefixWord ++ tailWord_4906263).sum := by decide
  have hdescent : baseEnd_4906263 < baseStart_4906263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906280 : List Nat := [2, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3]
def baseStart_4906280 : Nat := 118140960795 + 4906280 * 2 ^ 59
def prefixEnd_4906280 : Nat := 4983230072969 + 3 ^ 40 * 4906280 * 2
def baseEnd_4906280 : Nat := 2519279865541169390636435

theorem tailTrace_4906280 : CollatzResearch.WordTrace tailWord_4906280 prefixEnd_4906280 2519279865541169390636435 := by
  unfold tailWord_4906280
  simp only [CollatzResearch.WordTrace]
  refine ⟨89473366332696480379210147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119297821776928640505613529 89473366332696480379210147)
  ·
    refine ⟨134210049499044720568815221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89473366332696480379210147 134210049499044720568815221)
    ·
      refine ⟨12582192140535442553326427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134210049499044720568815221 12582192140535442553326427)
      ·
        refine ⟨18873288210803163829989641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582192140535442553326427 18873288210803163829989641)
        ·
          refine ⟨14154966158102372872492231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18873288210803163829989641 14154966158102372872492231)
          ·
            refine ⟨21232449237153559308738347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14154966158102372872492231 21232449237153559308738347)
            ·
              refine ⟨31848673855730338963107521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21232449237153559308738347 31848673855730338963107521)
              ·
                refine ⟨23886505391797754222330641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31848673855730338963107521 23886505391797754222330641)
                ·
                  refine ⟨17914879043848315666747981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23886505391797754222330641 17914879043848315666747981)
                  ·
                    refine ⟨6718079641443118375030493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17914879043848315666747981 6718079641443118375030493)
                    ·
                      refine ⟨2519279865541169390636435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718079641443118375030493 2519279865541169390636435)
                      ·
                        rfl

theorem cell23_4906280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 2, 2, 3, 3].length) (baseStart_4906280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906280 prefixEnd_4906280 := by exact prefixLift 4906280
  have htrace : WordTrace (prefixWord ++ tailWord_4906280) baseStart_4906280 baseEnd_4906280 := by
    simpa [prefixWord, tailWord_4906280, baseEnd_4906280] using wordTrace_append hprefix tailTrace_4906280
  have hstable : (prefixWord ++ tailWord_4906280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906280).length < 2 ^ (prefixWord ++ tailWord_4906280).sum := by decide
  have hdescent : baseEnd_4906280 < baseStart_4906280 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906303 : List Nat := [1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4]
def baseStart_4906303 : Nat := 118140960795 + 4906303 * 2 ^ 59
def prefixEnd_4906303 : Nat := 4983230072969 + 3 ^ 40 * 4906303 * 2
def baseEnd_4906303 : Nat := 2519291675596222800648829

theorem tailTrace_4906303 : CollatzResearch.WordTrace tailWord_4906303 prefixEnd_4906303 2519291675596222800648829 := by
  unfold tailWord_4906303
  simp only [CollatzResearch.WordTrace]
  refine ⟨178947571544309635686507563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119298381029539757124338375 178947571544309635686507563)
  ·
    refine ⟨268421357316464453529761345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178947571544309635686507563 268421357316464453529761345)
    ·
      refine ⟨201316017987348340147321009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268421357316464453529761345 201316017987348340147321009)
      ·
        refine ⟨150987013490511255110490757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201316017987348340147321009 150987013490511255110490757)
        ·
          refine ⟨28310065029470860333217017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 150987013490511255110490757 28310065029470860333217017)
          ·
            refine ⟨21232548772103145249912763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28310065029470860333217017 21232548772103145249912763)
            ·
              refine ⟨31848823158154717874869145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21232548772103145249912763 31848823158154717874869145)
              ·
                refine ⟨23886617368616038406151859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31848823158154717874869145 23886617368616038406151859)
                ·
                  refine ⟨35829926052924057609227789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23886617368616038406151859 35829926052924057609227789)
                  ·
                    refine ⟨13436222269846521603460421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35829926052924057609227789 13436222269846521603460421)
                    ·
                      refine ⟨2519291675596222800648829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13436222269846521603460421 2519291675596222800648829)
                      ·
                        rfl

theorem cell23_4906303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 2, 1, 2, 1, 3, 4].length) (baseStart_4906303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906303 prefixEnd_4906303 := by exact prefixLift 4906303
  have htrace : WordTrace (prefixWord ++ tailWord_4906303) baseStart_4906303 baseEnd_4906303 := by
    simpa [prefixWord, tailWord_4906303, baseEnd_4906303] using wordTrace_append hprefix tailTrace_4906303
  have hstable : (prefixWord ++ tailWord_4906303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906303).length < 2 ^ (prefixWord ++ tailWord_4906303).sum := by decide
  have hdescent : baseEnd_4906303 < baseStart_4906303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906323 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3]
def baseStart_4906323 : Nat := 118140960795 + 4906323 * 2 ^ 59
def prefixEnd_4906323 : Nat := 4983230072969 + 3 ^ 40 * 4906323 * 2
def baseEnd_4906323 : Nat := 2519301945209312722398737

theorem tailTrace_4906323 : CollatzResearch.WordTrace tailWord_4906323 prefixEnd_4906323 2519301945209312722398737 := by
  unfold tailWord_4906323
  simp only [CollatzResearch.WordTrace]
  refine ⟨178948301004237179102235623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119298867336158119401490415 178948301004237179102235623)
  ·
    refine ⟨268422451506355768653353435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178948301004237179102235623 268422451506355768653353435)
    ·
      refine ⟨402633677259533652980030153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268422451506355768653353435 402633677259533652980030153)
      ·
        refine ⟨301975257944650239735022615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402633677259533652980030153 301975257944650239735022615)
        ·
          refine ⟨452962886916975359602533923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 301975257944650239735022615 452962886916975359602533923)
          ·
            refine ⟨679444330375463039403800885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 452962886916975359602533923 679444330375463039403800885)
            ·
              refine ⟨63697905972699659944106333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 679444330375463039403800885 63697905972699659944106333)
              ·
                refine ⟨23886714739762372479039875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63697905972699659944106333 23886714739762372479039875)
                ·
                  refine ⟨35830072109643558718559813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23886714739762372479039875 35830072109643558718559813)
                  ·
                    refine ⟨6718138520558167259729965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35830072109643558718559813 6718138520558167259729965)
                    ·
                      refine ⟨2519301945209312722398737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718138520558167259729965 2519301945209312722398737)
                      ·
                        rfl

theorem cell23_4906323_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 1, 4, 3].length) (baseStart_4906323 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906323 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906323 prefixEnd_4906323 := by exact prefixLift 4906323
  have htrace : WordTrace (prefixWord ++ tailWord_4906323) baseStart_4906323 baseEnd_4906323 := by
    simpa [prefixWord, tailWord_4906323, baseEnd_4906323] using wordTrace_append hprefix tailTrace_4906323
  have hstable : (prefixWord ++ tailWord_4906323).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906323).length < 2 ^ (prefixWord ++ tailWord_4906323).sum := by decide
  have hdescent : baseEnd_4906323 < baseStart_4906323 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906323) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906340 : List Nat := [2, 3, 1, 1, 3, 2, 1, 1, 4, 2, 3]
def baseStart_4906340 : Nat := 118140960795 + 4906340 * 2 ^ 59
def prefixEnd_4906340 : Nat := 4983230072969 + 3 ^ 40 * 4906340 * 2
def baseEnd_4906340 : Nat := 2519310674380439155886159

theorem tailTrace_4906340 : CollatzResearch.WordTrace tailWord_4906340 prefixEnd_4906340 2519310674380439155886159 := by
  unfold tailWord_4906340
  simp only [CollatzResearch.WordTrace]
  refine ⟨89474460522587795502802237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119299280696783727337069649 89474460522587795502802237)
  ·
    refine ⟨33552922695970423313550839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89474460522587795502802237 33552922695970423313550839)
    ·
      refine ⟨50329384043955634970326259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33552922695970423313550839 50329384043955634970326259)
      ·
        refine ⟨75494076065933452455489389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50329384043955634970326259 75494076065933452455489389)
        ·
          refine ⟨28310278524725044670808521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75494076065933452455489389 28310278524725044670808521)
          ·
            refine ⟨21232708893543783503106391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28310278524725044670808521 21232708893543783503106391)
            ·
              refine ⟨31849063340315675254659587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21232708893543783503106391 31849063340315675254659587)
              ·
                refine ⟨47773595010473512881989381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31849063340315675254659587 47773595010473512881989381)
                ·
                  refine ⟨8957549064463783665373009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47773595010473512881989381 8957549064463783665373009)
                  ·
                    refine ⟨6718161798347837749029757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8957549064463783665373009 6718161798347837749029757)
                    ·
                      refine ⟨2519310674380439155886159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718161798347837749029757 2519310674380439155886159)
                      ·
                        rfl

theorem cell23_4906340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 1, 1, 4, 2, 3].length) (baseStart_4906340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906340 prefixEnd_4906340 := by exact prefixLift 4906340
  have htrace : WordTrace (prefixWord ++ tailWord_4906340) baseStart_4906340 baseEnd_4906340 := by
    simpa [prefixWord, tailWord_4906340, baseEnd_4906340] using wordTrace_append hprefix tailTrace_4906340
  have hstable : (prefixWord ++ tailWord_4906340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906340).length < 2 ^ (prefixWord ++ tailWord_4906340).sum := by decide
  have hdescent : baseEnd_4906340 < baseStart_4906340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906403 : List Nat := [1, 1, 1, 4, 1, 3, 1, 2, 3, 6]
def baseStart_4906403 : Nat := 118140960795 + 4906403 * 2 ^ 59
def prefixEnd_4906403 : Nat := 4983230072969 + 3 ^ 40 * 4906403 * 2
def baseEnd_4906403 : Nat := 839781007887224136466123

theorem tailTrace_4906403 : CollatzResearch.WordTrace tailWord_4906403 prefixEnd_4906403 839781007887224136466123 := by
  unfold tailWord_4906403
  simp only [CollatzResearch.WordTrace]
  refine ⟨178951218843947352765147863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119300812562631568510098575 178951218843947352765147863)
  ·
    refine ⟨268426828265921029147721795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178951218843947352765147863 268426828265921029147721795)
    ·
      refine ⟨402640242398881543721582693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268426828265921029147721795 402640242398881543721582693)
      ·
        refine ⟨75495045449790289447796755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402640242398881543721582693 75495045449790289447796755)
        ·
          refine ⟨113242568174685434171695133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75495045449790289447796755 113242568174685434171695133)
          ·
            refine ⟨42465963065507037814385675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113242568174685434171695133 42465963065507037814385675)
            ·
              refine ⟨63698944598260556721578513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42465963065507037814385675 63698944598260556721578513)
              ·
                refine ⟨47774208448695417541183885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63698944598260556721578513 47774208448695417541183885)
                ·
                  refine ⟨17915328168260781577943957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47774208448695417541183885 17915328168260781577943957)
                  ·
                    refine ⟨839781007887224136466123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17915328168260781577943957 839781007887224136466123)
                    ·
                      rfl

theorem cell23_4906403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 1, 2, 3, 6].length) (baseStart_4906403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906403 prefixEnd_4906403 := by exact prefixLift 4906403
  have htrace : WordTrace (prefixWord ++ tailWord_4906403) baseStart_4906403 baseEnd_4906403 := by
    simpa [prefixWord, tailWord_4906403, baseEnd_4906403] using wordTrace_append hprefix tailTrace_4906403
  have hstable : (prefixWord ++ tailWord_4906403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906403).length < 2 ^ (prefixWord ++ tailWord_4906403).sum := by decide
  have hdescent : baseEnd_4906403 < baseStart_4906403 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906440 : List Nat := [2, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4]
def baseStart_4906440 : Nat := 118140960795 + 4906440 * 2 ^ 59
def prefixEnd_4906440 : Nat := 4983230072969 + 3 ^ 40 * 4906440 * 2
def baseEnd_4906440 : Nat := 2519362022445888764635699

theorem tailTrace_4906440 : CollatzResearch.WordTrace tailWord_4906440 prefixEnd_4906440 2519362022445888764635699 := by
  unfold tailWord_4906440
  simp only [CollatzResearch.WordTrace]
  refine ⟨89476284172406654042122387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119301712229875538722829849 89476284172406654042122387)
  ·
    refine ⟨134214426258609981063183581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89476284172406654042122387 134214426258609981063183581)
    ·
      refine ⟨50330409846978742898693843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134214426258609981063183581 50330409846978742898693843)
      ·
        refine ⟨75495614770468114348040765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50330409846978742898693843 75495614770468114348040765)
        ·
          refine ⟨28310855538925542880515287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75495614770468114348040765 28310855538925542880515287)
          ·
            refine ⟨42466283308388314320772931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28310855538925542880515287 42466283308388314320772931)
            ·
              refine ⟨63699424962582471481159397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42466283308388314320772931 63699424962582471481159397)
              ·
                refine ⟨11943642180484213402717387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63699424962582471481159397 11943642180484213402717387)
                ·
                  refine ⟨17915463270726320104076081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11943642180484213402717387 17915463270726320104076081)
                  ·
                    refine ⟨13436597453044740078057061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17915463270726320104076081 13436597453044740078057061)
                    ·
                      refine ⟨2519362022445888764635699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13436597453044740078057061 2519362022445888764635699)
                      ·
                        rfl

theorem cell23_4906440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 1, 4, 1, 2, 4].length) (baseStart_4906440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906440 prefixEnd_4906440 := by exact prefixLift 4906440
  have htrace : WordTrace (prefixWord ++ tailWord_4906440) baseStart_4906440 baseEnd_4906440 := by
    simpa [prefixWord, tailWord_4906440, baseEnd_4906440] using wordTrace_append hprefix tailTrace_4906440
  have hstable : (prefixWord ++ tailWord_4906440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906440).length < 2 ^ (prefixWord ++ tailWord_4906440).sum := by decide
  have hdescent : baseEnd_4906440 < baseStart_4906440 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906444 : List Nat := [2, 2, 1, 4, 2, 1, 4, 1, 1, 1, 4]
def baseStart_4906444 : Nat := 118140960795 + 4906444 * 2 ^ 59
def prefixEnd_4906444 : Nat := 4983230072969 + 3 ^ 40 * 4906444 * 2
def baseEnd_4906444 : Nat := 2519364076368506748985681

theorem tailTrace_4906444 : CollatzResearch.WordTrace tailWord_4906444 prefixEnd_4906444 2519364076368506748985681 := by
  unfold tailWord_4906444
  simp only [CollatzResearch.WordTrace]
  refine ⟨89476357118399408383695193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119301809491199211178260257 89476357118399408383695193)
  ·
    refine ⟨67107267838799556287771395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89476357118399408383695193 67107267838799556287771395)
    ·
      refine ⟨100660901758199334431657093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67107267838799556287771395 100660901758199334431657093)
      ·
        refine ⟨18873919079662375205935705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100660901758199334431657093 18873919079662375205935705)
        ·
          refine ⟨14155439309746781404451779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18873919079662375205935705 14155439309746781404451779)
          ·
            refine ⟨21233158964620172106677669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14155439309746781404451779 21233158964620172106677669)
            ·
              refine ⟨3981217305866282270002063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21233158964620172106677669 3981217305866282270002063)
              ·
                refine ⟨5971825958799423405003095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981217305866282270002063 5971825958799423405003095)
                ·
                  refine ⟨8957738938199135107504643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5971825958799423405003095 8957738938199135107504643)
                  ·
                    refine ⟨13436608407298702661256965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8957738938199135107504643 13436608407298702661256965)
                    ·
                      refine ⟨2519364076368506748985681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13436608407298702661256965 2519364076368506748985681)
                      ·
                        rfl

theorem cell23_4906444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_4906444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906444 prefixEnd_4906444 := by exact prefixLift 4906444
  have htrace : WordTrace (prefixWord ++ tailWord_4906444) baseStart_4906444 baseEnd_4906444 := by
    simpa [prefixWord, tailWord_4906444, baseEnd_4906444] using wordTrace_append hprefix tailTrace_4906444
  have hstable : (prefixWord ++ tailWord_4906444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906444).length < 2 ^ (prefixWord ++ tailWord_4906444).sum := by decide
  have hdescent : baseEnd_4906444 < baseStart_4906444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906454 : List Nat := [5, 2, 1, 1, 1, 3, 1, 1, 4, 4]
def baseStart_4906454 : Nat := 118140960795 + 4906454 * 2 ^ 59
def prefixEnd_4906454 : Nat := 4983230072969 + 3 ^ 40 * 4906454 * 2
def baseEnd_4906454 : Nat := 839789737058350569953545

theorem tailTrace_4906454 : CollatzResearch.WordTrace tailWord_4906454 prefixEnd_4906454 839789737058350569953545 := by
  unfold tailWord_4906454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11184567435422661779703401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119302052644508392316836277 11184567435422661779703401)
  ·
    refine ⟨8388425576566996334777551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11184567435422661779703401 8388425576566996334777551)
    ·
      refine ⟨12582638364850494502166327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8388425576566996334777551 12582638364850494502166327)
      ·
        refine ⟨18873957547275741753249491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582638364850494502166327 18873957547275741753249491)
        ·
          refine ⟨28310936320913612629874237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18873957547275741753249491 28310936320913612629874237)
          ·
            refine ⟨10616601120342604736202839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28310936320913612629874237 10616601120342604736202839)
            ·
              refine ⟨15924901680513907104304259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10616601120342604736202839 15924901680513907104304259)
              ·
                refine ⟨23887352520770860656456389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15924901680513907104304259 23887352520770860656456389)
                ·
                  refine ⟨4478878597644536373085573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23887352520770860656456389 4478878597644536373085573)
                  ·
                    refine ⟨839789737058350569953545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4478878597644536373085573 839789737058350569953545)
                    ·
                      rfl

theorem cell23_4906454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_4906454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906454 prefixEnd_4906454 := by exact prefixLift 4906454
  have htrace : WordTrace (prefixWord ++ tailWord_4906454) baseStart_4906454 baseEnd_4906454 := by
    simpa [prefixWord, tailWord_4906454, baseEnd_4906454] using wordTrace_append hprefix tailTrace_4906454
  have hstable : (prefixWord ++ tailWord_4906454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906454).length < 2 ^ (prefixWord ++ tailWord_4906454).sum := by decide
  have hdescent : baseEnd_4906454 < baseStart_4906454 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906461 : List Nat := [1, 4, 3, 1, 1, 3, 2, 1, 3, 2, 2]
def baseStart_4906461 : Nat := 118140960795 + 4906461 * 2 ^ 59
def prefixEnd_4906461 : Nat := 4983230072969 + 3 ^ 40 * 4906461 * 2
def baseEnd_4906461 : Nat := 2519372805539633182473103

theorem tailTrace_4906461 : CollatzResearch.WordTrace tailWord_4906461 prefixEnd_4906461 2519372805539633182473103 := by
  unfold tailWord_4906461
  simp only [CollatzResearch.WordTrace]
  refine ⟨178953334277737228670759237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119302222851824819113839491 178953334277737228670759237)
  ·
    refine ⟨33553750177075730375767357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178953334277737228670759237 33553750177075730375767357)
    ·
      refine ⟨12582656316403398890912759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33553750177075730375767357 12582656316403398890912759)
      ·
        refine ⟨18873984474605098336369139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12582656316403398890912759 18873984474605098336369139)
        ·
          refine ⟨28310976711907647504553709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18873984474605098336369139 28310976711907647504553709)
          ·
            refine ⟨10616616266965367814207641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28310976711907647504553709 10616616266965367814207641)
            ·
              refine ⟨7962462200224025860655731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10616616266965367814207641 7962462200224025860655731)
              ·
                refine ⟨11943693300336038790983597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7962462200224025860655731 11943693300336038790983597)
                ·
                  refine ⟨4478884987626014546618849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11943693300336038790983597 4478884987626014546618849)
                  ·
                    refine ⟨3359163740719510909964137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4478884987626014546618849 3359163740719510909964137)
                    ·
                      refine ⟨2519372805539633182473103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359163740719510909964137 2519372805539633182473103)
                      ·
                        rfl

theorem cell23_4906461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 3, 2, 1, 3, 2, 2].length) (baseStart_4906461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906461 prefixEnd_4906461 := by exact prefixLift 4906461
  have htrace : WordTrace (prefixWord ++ tailWord_4906461) baseStart_4906461 baseEnd_4906461 := by
    simpa [prefixWord, tailWord_4906461, baseEnd_4906461] using wordTrace_append hprefix tailTrace_4906461
  have hstable : (prefixWord ++ tailWord_4906461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906461).length < 2 ^ (prefixWord ++ tailWord_4906461).sum := by decide
  have hdescent : baseEnd_4906461 < baseStart_4906461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906474 : List Nat := [3, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4]
def baseStart_4906474 : Nat := 118140960795 + 4906474 * 2 ^ 59
def prefixEnd_4906474 : Nat := 4983230072969 + 3 ^ 40 * 4906474 * 2
def baseEnd_4906474 : Nat := 2519379480788141631610543

theorem tailTrace_4906474 : CollatzResearch.WordTrace tailWord_4906474 prefixEnd_4906474 2519379480788141631610543 := by
  unfold tailWord_4906474
  simp only [CollatzResearch.WordTrace]
  refine ⟨44738452106672532972745619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119302538951126754593988317 44738452106672532972745619)
  ·
    refine ⟨67107678160008799459118429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44738452106672532972745619 67107678160008799459118429)
    ·
      refine ⟨25165379310003299797169411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67107678160008799459118429 25165379310003299797169411)
      ·
        refine ⟨37748068965004949695754117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25165379310003299797169411 37748068965004949695754117)
        ·
          refine ⟨7077762930938428067953897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37748068965004949695754117 7077762930938428067953897)
          ·
            refine ⟨5308322198203821050965423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7077762930938428067953897 5308322198203821050965423)
            ·
              refine ⟨7962483297305731576448135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5308322198203821050965423 7962483297305731576448135)
              ·
                refine ⟨11943724945958597364672203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7962483297305731576448135 11943724945958597364672203)
                ·
                  refine ⟨17915587418937896047008305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11943724945958597364672203 17915587418937896047008305)
                  ·
                    refine ⟨13436690564203422035256229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17915587418937896047008305 13436690564203422035256229)
                    ·
                      refine ⟨2519379480788141631610543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13436690564203422035256229 2519379480788141631610543)
                      ·
                        rfl

theorem cell23_4906474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 4, 2, 1, 1, 1, 2, 4].length) (baseStart_4906474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906474 prefixEnd_4906474 := by exact prefixLift 4906474
  have htrace : WordTrace (prefixWord ++ tailWord_4906474) baseStart_4906474 baseEnd_4906474 := by
    simpa [prefixWord, tailWord_4906474, baseEnd_4906474] using wordTrace_append hprefix tailTrace_4906474
  have hstable : (prefixWord ++ tailWord_4906474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906474).length < 2 ^ (prefixWord ++ tailWord_4906474).sum := by decide
  have hdescent : baseEnd_4906474 < baseStart_4906474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906483 : List Nat := [1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8]
def baseStart_4906483 : Nat := 118140960795 + 4906483 * 2 ^ 59
def prefixEnd_4906483 : Nat := 4983230072969 + 3 ^ 40 * 4906483 * 2
def baseEnd_4906483 : Nat := 2519384102114032096398001

theorem tailTrace_4906483 : CollatzResearch.WordTrace tailWord_4906483 prefixEnd_4906483 2519384102114032096398001 := by
  unfold tailWord_4906483
  simp only [CollatzResearch.WordTrace]
  refine ⟨178954136683657526428060103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119302757789105017618706735 178954136683657526428060103)
  ·
    refine ⟨268431205025486289642090155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178954136683657526428060103 268431205025486289642090155)
    ·
      refine ⟨402646807538229434463135233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268431205025486289642090155 402646807538229434463135233)
      ·
        refine ⟨301985105653672075847351425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402646807538229434463135233 301985105653672075847351425)
        ·
          refine ⟨226488829240254056885513569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 301985105653672075847351425 226488829240254056885513569)
          ·
            refine ⟨169866621930190542664135177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226488829240254056885513569 169866621930190542664135177)
            ·
              refine ⟨127399966447642906998101383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169866621930190542664135177 127399966447642906998101383)
              ·
                refine ⟨191099949671464360497152075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127399966447642906998101383 191099949671464360497152075)
                ·
                  refine ⟨286649924507196540745728113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191099949671464360497152075 286649924507196540745728113)
                  ·
                    refine ⟨214987443380397405559296085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 286649924507196540745728113 214987443380397405559296085)
                    ·
                      refine ⟨2519384102114032096398001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 214987443380397405559296085 2519384102114032096398001)
                      ·
                        rfl

theorem cell23_4906483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 1, 1, 2, 8].length) (baseStart_4906483 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906483 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906483 prefixEnd_4906483 := by exact prefixLift 4906483
  have htrace : WordTrace (prefixWord ++ tailWord_4906483) baseStart_4906483 baseEnd_4906483 := by
    simpa [prefixWord, tailWord_4906483, baseEnd_4906483] using wordTrace_append hprefix tailTrace_4906483
  have hstable : (prefixWord ++ tailWord_4906483).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906483).length < 2 ^ (prefixWord ++ tailWord_4906483).sum := by decide
  have hdescent : baseEnd_4906483 < baseStart_4906483 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906504 : List Nat := [2, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2]
def baseStart_4906504 : Nat := 118140960795 + 4906504 * 2 ^ 59
def prefixEnd_4906504 : Nat := 4983230072969 + 3 ^ 40 * 4906504 * 2
def baseEnd_4906504 : Nat := 2519394885207776514235405

theorem tailTrace_4906504 : CollatzResearch.WordTrace tailWord_4906504 prefixEnd_4906504 2519394885207776514235405 := by
  unfold tailWord_4906504
  simp only [CollatzResearch.WordTrace]
  refine ⟨89477451308290723507287283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119303268411054298009716377 89477451308290723507287283)
  ·
    refine ⟨134216176962436085260930925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89477451308290723507287283 134216176962436085260930925)
    ·
      refine ⟨50331066360913531972849097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134216176962436085260930925 50331066360913531972849097)
      ·
        refine ⟨37748299770685148979636823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50331066360913531972849097 37748299770685148979636823)
        ·
          refine ⟨56622449656027723469455235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37748299770685148979636823 56622449656027723469455235)
          ·
            refine ⟨84933674484041585204182853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56622449656027723469455235 84933674484041585204182853)
            ·
              refine ⟨15925063965757797225784285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84933674484041585204182853 15925063965757797225784285)
              ·
                refine ⟨5971898987159173959669107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15925063965757797225784285 5971898987159173959669107)
                ·
                  refine ⟨8957848480738760939503661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5971898987159173959669107 8957848480738760939503661)
                  ·
                    refine ⟨3359193180277035352313873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8957848480738760939503661 3359193180277035352313873)
                    ·
                      refine ⟨2519394885207776514235405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359193180277035352313873 2519394885207776514235405)
                      ·
                        rfl

theorem cell23_4906504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 4, 3, 1, 3, 2].length) (baseStart_4906504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906504 prefixEnd_4906504 := by exact prefixLift 4906504
  have htrace : WordTrace (prefixWord ++ tailWord_4906504) baseStart_4906504 baseEnd_4906504 := by
    simpa [prefixWord, tailWord_4906504, baseEnd_4906504] using wordTrace_append hprefix tailTrace_4906504
  have hstable : (prefixWord ++ tailWord_4906504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906504).length < 2 ^ (prefixWord ++ tailWord_4906504).sum := by decide
  have hdescent : baseEnd_4906504 < baseStart_4906504 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906528 : List Nat := [2, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4906528 : Nat := 118140960795 + 4906528 * 2 ^ 59
def prefixEnd_4906528 : Nat := 4983230072969 + 3 ^ 40 * 4906528 * 2
def baseEnd_4906528 : Nat := 2519407208743484420335295

theorem tailTrace_4906528 : CollatzResearch.WordTrace tailWord_4906528 prefixEnd_4906528 2519407208743484420335295 := by
  unfold tailWord_4906528
  simp only [CollatzResearch.WordTrace]
  refine ⟨89477888984247249556724119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119303851978996332742298825 89477888984247249556724119)
  ·
    refine ⟨134216833476370874335086179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89477888984247249556724119 134216833476370874335086179)
    ·
      refine ⟨201325250214556311502629269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134216833476370874335086179 201325250214556311502629269)
      ·
        refine ⟨9437121103807327101685747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 201325250214556311502629269 9437121103807327101685747)
        ·
          refine ⟨14155681655710990652528621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9437121103807327101685747 14155681655710990652528621)
          ·
            refine ⟨5308380620891621494698233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14155681655710990652528621 5308380620891621494698233)
            ·
              refine ⟨3981285465668716121023675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5308380620891621494698233 3981285465668716121023675)
              ·
                refine ⟨5971928198503074181535513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981285465668716121023675 5971928198503074181535513)
                ·
                  refine ⟨4478946148877305636151635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5971928198503074181535513 4478946148877305636151635)
                  ·
                    refine ⟨6718419223315958454227453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4478946148877305636151635 6718419223315958454227453)
                    ·
                      refine ⟨2519407208743484420335295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718419223315958454227453 2519407208743484420335295)
                      ·
                        rfl

theorem cell23_4906528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4906528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906528 prefixEnd_4906528 := by exact prefixLift 4906528
  have htrace : WordTrace (prefixWord ++ tailWord_4906528) baseStart_4906528 baseEnd_4906528 := by
    simpa [prefixWord, tailWord_4906528, baseEnd_4906528] using wordTrace_append hprefix tailTrace_4906528
  have hstable : (prefixWord ++ tailWord_4906528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906528).length < 2 ^ (prefixWord ++ tailWord_4906528).sum := by decide
  have hdescent : baseEnd_4906528 < baseStart_4906528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906577 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 1, 7, 2]
def baseStart_4906577 : Nat := 118140960795 + 4906577 * 2 ^ 59
def prefixEnd_4906577 : Nat := 4983230072969 + 3 ^ 40 * 4906577 * 2
def baseEnd_4906577 : Nat := 2519432369295554728622569

theorem tailTrace_4906577 : CollatzResearch.WordTrace tailWord_4906577 prefixEnd_4906577 2519432369295554728622569 := by
  unfold tailWord_4906577
  simp only [CollatzResearch.WordTrace]
  refine ⟨178957565145316980481981985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119305043430211320321321323 178957565145316980481981985)
  ·
    refine ⟨134218173858987735361486489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178957565145316980481981985 134218173858987735361486489)
    ·
      refine ⟨100663630394240801521114867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134218173858987735361486489 100663630394240801521114867)
      ·
        refine ⟨150995445591361202281672301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100663630394240801521114867 150995445591361202281672301)
        ·
          refine ⟨56623292096760450855627113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150995445591361202281672301 56623292096760450855627113)
          ·
            refine ⟨42467469072570338141720335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56623292096760450855627113 42467469072570338141720335)
            ·
              refine ⟨63701203608855507212580503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42467469072570338141720335 63701203608855507212580503)
              ·
                refine ⟨95551805413283260818870755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63701203608855507212580503 95551805413283260818870755)
                ·
                  refine ⟨143327708119924891228306133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95551805413283260818870755 143327708119924891228306133)
                  ·
                    refine ⟨3359243159060739638163425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 143327708119924891228306133 3359243159060739638163425)
                    ·
                      refine ⟨2519432369295554728622569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359243159060739638163425 2519432369295554728622569)
                      ·
                        rfl

theorem cell23_4906577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 7, 2].length) (baseStart_4906577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906577 prefixEnd_4906577 := by exact prefixLift 4906577
  have htrace : WordTrace (prefixWord ++ tailWord_4906577) baseStart_4906577 baseEnd_4906577 := by
    simpa [prefixWord, tailWord_4906577, baseEnd_4906577] using wordTrace_append hprefix tailTrace_4906577
  have hstable : (prefixWord ++ tailWord_4906577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906577).length < 2 ^ (prefixWord ++ tailWord_4906577).sum := by decide
  have hdescent : baseEnd_4906577 < baseStart_4906577 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906607 : List Nat := [1, 1, 2, 1, 3, 2, 1, 1, 3, 6, 2]
def baseStart_4906607 : Nat := 118140960795 + 4906607 * 2 ^ 59
def prefixEnd_4906607 : Nat := 4983230072969 + 3 ^ 40 * 4906607 * 2
def baseEnd_4906607 : Nat := 2519447773715189611247431

theorem tailTrace_4906607 : CollatzResearch.WordTrace tailWord_4906607 prefixEnd_4906607 2519447773715189611247431 := by
  unfold tailWord_4906607
  simp only [CollatzResearch.WordTrace]
  refine ⟨178958659335208295605574075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119305772890138863737049383 178958659335208295605574075)
  ·
    refine ⟨268437989002812443408361113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178958659335208295605574075 268437989002812443408361113)
    ·
      refine ⟨201328491752109332556270835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268437989002812443408361113 201328491752109332556270835)
      ·
        refine ⟨301992737628163998834406253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201328491752109332556270835 301992737628163998834406253)
        ·
          refine ⟨113247276610561499562902345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 301992737628163998834406253 113247276610561499562902345)
          ·
            refine ⟨84935457457921124672176759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113247276610561499562902345 84935457457921124672176759)
            ·
              refine ⟨127403186186881687008265139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84935457457921124672176759 127403186186881687008265139)
              ·
                refine ⟨191104779280322530512397709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127403186186881687008265139 191104779280322530512397709)
                ·
                  refine ⟨71664292230120948942149141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191104779280322530512397709 71664292230120948942149141)
                  ·
                    refine ⟨3359263698286919481663241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71664292230120948942149141 3359263698286919481663241)
                    ·
                      refine ⟨2519447773715189611247431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359263698286919481663241 2519447773715189611247431)
                      ·
                        rfl

theorem cell23_4906607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 1, 3, 6, 2].length) (baseStart_4906607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906607 prefixEnd_4906607 := by exact prefixLift 4906607
  have htrace : WordTrace (prefixWord ++ tailWord_4906607) baseStart_4906607 baseEnd_4906607 := by
    simpa [prefixWord, tailWord_4906607, baseEnd_4906607] using wordTrace_append hprefix tailTrace_4906607
  have hstable : (prefixWord ++ tailWord_4906607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906607).length < 2 ^ (prefixWord ++ tailWord_4906607).sum := by decide
  have hdescent : baseEnd_4906607 < baseStart_4906607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906617 : List Nat := [1, 2, 1, 3, 3, 1, 1, 2, 5, 4]
def baseStart_4906617 : Nat := 118140960795 + 4906617 * 2 ^ 59
def prefixEnd_4906617 : Nat := 4983230072969 + 3 ^ 40 * 4906617 * 2
def baseEnd_4906617 : Nat := 839817636173911524040795

theorem tailTrace_4906617 : CollatzResearch.WordTrace tailWord_4906617 prefixEnd_4906617 839817636173911524040795 := by
  unfold tailWord_4906617
  simp only [CollatzResearch.WordTrace]
  refine ⟨178959024065172067313438105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119306016043448044875625403 178959024065172067313438105)
  ·
    refine ⟨134219268048879050485078579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178959024065172067313438105 134219268048879050485078579)
    ·
      refine ⟨201328902073318575727617869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134219268048879050485078579 201328902073318575727617869)
      ·
        refine ⟨75498338277494465897856701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201328902073318575727617869 75498338277494465897856701)
        ·
          refine ⟨28311876854060424711696263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75498338277494465897856701 28311876854060424711696263)
          ·
            refine ⟨42467815281090637067544395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28311876854060424711696263 42467815281090637067544395)
            ·
              refine ⟨63701722921635955601316593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42467815281090637067544395 63701722921635955601316593)
              ·
                refine ⟨47776292191226966700987445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63701722921635955601316593 47776292191226966700987445)
                ·
                  refine ⟨4479027392927528128217573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47776292191226966700987445 4479027392927528128217573)
                  ·
                    refine ⟨839817636173911524040795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479027392927528128217573 839817636173911524040795)
                    ·
                      rfl

theorem cell23_4906617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 2, 5, 4].length) (baseStart_4906617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906617 prefixEnd_4906617 := by exact prefixLift 4906617
  have htrace : WordTrace (prefixWord ++ tailWord_4906617) baseStart_4906617 baseEnd_4906617 := by
    simpa [prefixWord, tailWord_4906617, baseEnd_4906617] using wordTrace_append hprefix tailTrace_4906617
  have hstable : (prefixWord ++ tailWord_4906617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906617).length < 2 ^ (prefixWord ++ tailWord_4906617).sum := by decide
  have hdescent : baseEnd_4906617 < baseStart_4906617 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906627 : List Nat := [1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3]
def baseStart_4906627 : Nat := 118140960795 + 4906627 * 2 ^ 59
def prefixEnd_4906627 : Nat := 4983230072969 + 3 ^ 40 * 4906627 * 2
def baseEnd_4906627 : Nat := 2519458043328279532997339

theorem tailTrace_4906627 : CollatzResearch.WordTrace tailWord_4906627 prefixEnd_4906627 2519458043328279532997339 := by
  unfold tailWord_4906627
  simp only [CollatzResearch.WordTrace]
  refine ⟨178959388795135839021302135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119306259196757226014201423 178959388795135839021302135)
  ·
    refine ⟨268439083192703758531953203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178959388795135839021302135 268439083192703758531953203)
    ·
      refine ⟨402658624789055637797929805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268439083192703758531953203 402658624789055637797929805)
      ·
        refine ⟨150996984295895864174223677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402658624789055637797929805 150996984295895864174223677)
        ·
          refine ⟨56623869110960949065333879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 150996984295895864174223677 56623869110960949065333879)
          ·
            refine ⟨84935803666441423598000819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56623869110960949065333879 84935803666441423598000819)
            ·
              refine ⟨127403705499662135397001229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84935803666441423598000819 127403705499662135397001229)
              ·
                refine ⟨47776389562373300773875461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127403705499662135397001229 47776389562373300773875461)
                ·
                  refine ⟨8958073042944993895101649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47776389562373300773875461 8958073042944993895101649)
                  ·
                    refine ⟨6718554782208745421326237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8958073042944993895101649 6718554782208745421326237)
                    ·
                      refine ⟨2519458043328279532997339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718554782208745421326237 2519458043328279532997339)
                      ·
                        rfl

theorem cell23_4906627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 3, 4, 2, 3].length) (baseStart_4906627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906627 prefixEnd_4906627 := by exact prefixLift 4906627
  have htrace : WordTrace (prefixWord ++ tailWord_4906627) baseStart_4906627 baseEnd_4906627 := by
    simpa [prefixWord, tailWord_4906627, baseEnd_4906627] using wordTrace_append hprefix tailTrace_4906627
  have hstable : (prefixWord ++ tailWord_4906627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906627).length < 2 ^ (prefixWord ++ tailWord_4906627).sum := by decide
  have hdescent : baseEnd_4906627 < baseStart_4906627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906634 : List Nat := [3, 1, 2, 3, 2, 1, 1, 3, 3, 4]
def baseStart_4906634 : Nat := 118140960795 + 4906634 * 2 ^ 59
def prefixEnd_4906634 : Nat := 4983230072969 + 3 ^ 40 * 4906634 * 2
def baseEnd_4906634 : Nat := 839820545897620335203269

theorem tailTrace_4906634 : CollatzResearch.WordTrace tailWord_4906634 prefixEnd_4906634 839820545897620335203269 := by
  unfold tailWord_4906634
  simp only [CollatzResearch.WordTrace]
  refine ⟨44739911026527619804201739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119306429404073652811204637 44739911026527619804201739)
  ·
    refine ⟨67109866539791429706302609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44739911026527619804201739 67109866539791429706302609)
    ·
      refine ⟨50332399904843572279726957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67109866539791429706302609 50332399904843572279726957)
      ·
        refine ⟨18874649964316339604897609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50332399904843572279726957 18874649964316339604897609)
        ·
          refine ⟨14155987473237254703673207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18874649964316339604897609 14155987473237254703673207)
          ·
            refine ⟨21233981209855882055509811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14155987473237254703673207 21233981209855882055509811)
            ·
              refine ⟨31850971814783823083264717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21233981209855882055509811 31850971814783823083264717)
              ·
                refine ⟨11944114430543933656224269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31850971814783823083264717 11944114430543933656224269)
                ·
                  refine ⟨4479042911453975121084101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11944114430543933656224269 4479042911453975121084101)
                  ·
                    refine ⟨839820545897620335203269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479042911453975121084101 839820545897620335203269)
                    ·
                      rfl

theorem cell23_4906634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 1, 3, 3, 4].length) (baseStart_4906634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906634 prefixEnd_4906634 := by exact prefixLift 4906634
  have htrace : WordTrace (prefixWord ++ tailWord_4906634) baseStart_4906634 baseEnd_4906634 := by
    simpa [prefixWord, tailWord_4906634, baseEnd_4906634] using wordTrace_append hprefix tailTrace_4906634
  have hstable : (prefixWord ++ tailWord_4906634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906634).length < 2 ^ (prefixWord ++ tailWord_4906634).sum := by decide
  have hdescent : baseEnd_4906634 < baseStart_4906634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906674 : List Nat := [3, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_4906674 : Nat := 118140960795 + 4906674 * 2 ^ 59
def prefixEnd_4906674 : Nat := 4983230072969 + 3 ^ 40 * 4906674 * 2
def baseEnd_4906674 : Nat := 2519482176919040849109623

theorem tailTrace_4906674 : CollatzResearch.WordTrace tailWord_4906674 prefixEnd_4906674 2519482176919040849109623 := by
  unfold tailWord_4906674
  simp only [CollatzResearch.WordTrace]
  refine ⟨44740275756491391512065769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119307402017310377365508717 44740275756491391512065769)
  ·
    refine ⟨33555206817368543634049327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44740275756491391512065769 33555206817368543634049327)
    ·
      refine ⟨50332810226052815451073991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33555206817368543634049327 50332810226052815451073991)
      ·
        refine ⟨75499215339079223176610987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50332810226052815451073991 75499215339079223176610987)
        ·
          refine ⟨113248823008618834764916481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75499215339079223176610987 113248823008618834764916481)
          ·
            refine ⟨84936617256464126073687361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113248823008618834764916481 84936617256464126073687361)
            ·
              refine ⟨63702462942348094555265521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84936617256464126073687361 63702462942348094555265521)
              ·
                refine ⟨47776847206761070916449141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63702462942348094555265521 47776847206761070916449141)
                ·
                  refine ⟨4479079425633850398417107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47776847206761070916449141 4479079425633850398417107)
                  ·
                    refine ⟨6718619138450775597625661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479079425633850398417107 6718619138450775597625661)
                    ·
                      refine ⟨2519482176919040849109623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718619138450775597625661 2519482176919040849109623)
                      ·
                        rfl

theorem cell23_4906674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_4906674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906674 prefixEnd_4906674 := by exact prefixLift 4906674
  have htrace : WordTrace (prefixWord ++ tailWord_4906674) baseStart_4906674 baseEnd_4906674 := by
    simpa [prefixWord, tailWord_4906674, baseEnd_4906674] using wordTrace_append hprefix tailTrace_4906674
  have hstable : (prefixWord ++ tailWord_4906674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906674).length < 2 ^ (prefixWord ++ tailWord_4906674).sum := by decide
  have hdescent : baseEnd_4906674 < baseStart_4906674 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906678 : List Nat := [5, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3]
def baseStart_4906678 : Nat := 118140960795 + 4906678 * 2 ^ 59
def prefixEnd_4906678 : Nat := 4983230072969 + 3 ^ 40 * 4906678 * 2
def baseEnd_4906678 : Nat := 2519484230841658833459605

theorem tailTrace_4906678 : CollatzResearch.WordTrace tailWord_4906678 prefixEnd_4906678 2519484230841658833459605 := by
  unfold tailWord_4906678
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185078057371942170713043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119307499278634049820939125 11185078057371942170713043)
  ·
    refine ⟨16777617086057913256069565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11185078057371942170713043 16777617086057913256069565)
    ·
      refine ⟨6291606407271717471026087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16777617086057913256069565 6291606407271717471026087)
      ·
        refine ⟨9437409610907576206539131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6291606407271717471026087 9437409610907576206539131)
        ·
          refine ⟨14156114416361364309808697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9437409610907576206539131 14156114416361364309808697)
          ·
            refine ⟨10617085812271023232356523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14156114416361364309808697 10617085812271023232356523)
            ·
              refine ⟨15925628718406534848534785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10617085812271023232356523 15925628718406534848534785)
              ·
                refine ⟨11944221538804901136401089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15925628718406534848534785 11944221538804901136401089)
                ·
                  refine ⟨8958166154103675852300817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11944221538804901136401089 8958166154103675852300817)
                  ·
                    refine ⟨6718624615577756889225613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8958166154103675852300817 6718624615577756889225613)
                    ·
                      refine ⟨2519484230841658833459605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718624615577756889225613 2519484230841658833459605)
                      ·
                        rfl

theorem cell23_4906678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_4906678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906678 prefixEnd_4906678 := by exact prefixLift 4906678
  have htrace : WordTrace (prefixWord ++ tailWord_4906678) baseStart_4906678 baseEnd_4906678 := by
    simpa [prefixWord, tailWord_4906678, baseEnd_4906678] using wordTrace_append hprefix tailTrace_4906678
  have hstable : (prefixWord ++ tailWord_4906678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906678).length < 2 ^ (prefixWord ++ tailWord_4906678).sum := by decide
  have hdescent : baseEnd_4906678 < baseStart_4906678 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906698 : List Nat := [3, 1, 2, 1, 6, 1, 2, 1, 6]
def baseStart_4906698 : Nat := 118140960795 + 4906698 * 2 ^ 59
def prefixEnd_4906698 : Nat := 4983230072969 + 3 ^ 40 * 4906698 * 2
def baseEnd_4906698 : Nat := 279943833383860972801057

theorem tailTrace_4906698 : CollatzResearch.WordTrace tailWord_4906698 prefixEnd_4906698 279943833383860972801057 := by
  unfold tailWord_4906698
  simp only [CollatzResearch.WordTrace]
  refine ⟨44740494594469654536784187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119307985585252412098091165 44740494594469654536784187)
  ·
    refine ⟨67110741891704481805176281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44740494594469654536784187 67110741891704481805176281)
    ·
      refine ⟨50333056418778361353882211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67110741891704481805176281 50333056418778361353882211)
      ·
        refine ⟨75499584628167542030823317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50333056418778361353882211 75499584628167542030823317)
        ·
          refine ⟨3539043029445353532694843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 75499584628167542030823317 3539043029445353532694843)
          ·
            refine ⟨5308564544168030299042265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539043029445353532694843 5308564544168030299042265)
            ·
              refine ⟨3981423408126022724281699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5308564544168030299042265 3981423408126022724281699)
              ·
                refine ⟨5972135112189034086422549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981423408126022724281699 5972135112189034086422549)
                ·
                  refine ⟨279943833383860972801057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5972135112189034086422549 279943833383860972801057)
                  ·
                    rfl

theorem cell23_4906698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 2, 1, 6].length) (baseStart_4906698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906698 prefixEnd_4906698 := by exact prefixLift 4906698
  have htrace : WordTrace (prefixWord ++ tailWord_4906698) baseStart_4906698 baseEnd_4906698 := by
    simpa [prefixWord, tailWord_4906698, baseEnd_4906698] using wordTrace_append hprefix tailTrace_4906698
  have hstable : (prefixWord ++ tailWord_4906698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906698).length < 2 ^ (prefixWord ++ tailWord_4906698).sum := by decide
  have hdescent : baseEnd_4906698 < baseStart_4906698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906714 : List Nat := [3, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4]
def baseStart_4906714 : Nat := 118140960795 + 4906714 * 2 ^ 59
def prefixEnd_4906714 : Nat := 4983230072969 + 3 ^ 40 * 4906714 * 2
def baseEnd_4906714 : Nat := 2519502716145220692609439

theorem tailTrace_4906714 : CollatzResearch.WordTrace tailWord_4906714 prefixEnd_4906714 2519502716145220692609439 := by
  unfold tailWord_4906714
  simp only [CollatzResearch.WordTrace]
  refine ⟨44740640486455163219929799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119308374630547101919812797 44740640486455163219929799)
  ·
    refine ⟨67110960729682744829894699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44740640486455163219929799 67110960729682744829894699)
    ·
      refine ⟨100666441094524117244842049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67110960729682744829894699 100666441094524117244842049)
      ·
        refine ⟨75499830820893087933631537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100666441094524117244842049 75499830820893087933631537)
        ·
          refine ⟨56624873115669815950223653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75499830820893087933631537 56624873115669815950223653)
          ·
            refine ⟨10617163709188090490666935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56624873115669815950223653 10617163709188090490666935)
            ·
              refine ⟨15925745563782135736000403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10617163709188090490666935 15925745563782135736000403)
              ·
                refine ⟨23888618345673203604000605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15925745563782135736000403 23888618345673203604000605)
                ·
                  refine ⟨8958231879627451351500227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23888618345673203604000605 8958231879627451351500227)
                  ·
                    refine ⟨13437347819441177027250341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8958231879627451351500227 13437347819441177027250341)
                    ·
                      refine ⟨2519502716145220692609439, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13437347819441177027250341 2519502716145220692609439)
                      ·
                        rfl

theorem cell23_4906714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 1, 1, 3, 1, 4].length) (baseStart_4906714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906714 prefixEnd_4906714 := by exact prefixLift 4906714
  have htrace : WordTrace (prefixWord ++ tailWord_4906714) baseStart_4906714 baseEnd_4906714 := by
    simpa [prefixWord, tailWord_4906714, baseEnd_4906714] using wordTrace_append hprefix tailTrace_4906714
  have hstable : (prefixWord ++ tailWord_4906714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906714).length < 2 ^ (prefixWord ++ tailWord_4906714).sum := by decide
  have hdescent : baseEnd_4906714 < baseStart_4906714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906742 : List Nat := [5, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3]
def baseStart_4906742 : Nat := 118140960795 + 4906742 * 2 ^ 59
def prefixEnd_4906742 : Nat := 4983230072969 + 3 ^ 40 * 4906742 * 2
def baseEnd_4906742 : Nat := 2519517093603546583059311

theorem tailTrace_4906742 : CollatzResearch.WordTrace tailWord_4906742 prefixEnd_4906742 2519517093603546583059311 := by
  unfold tailWord_4906742
  simp only [CollatzResearch.WordTrace]
  refine ⟨11185223949357450853858655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119309055459812809107825653 11185223949357450853858655)
  ·
    refine ⟨16777835924036176280787983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11185223949357450853858655 16777835924036176280787983)
    ·
      refine ⟨25166753886054264421181975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16777835924036176280787983 25166753886054264421181975)
      ·
        refine ⟨37750130829081396631772963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25166753886054264421181975 37750130829081396631772963)
        ·
          refine ⟨56625196243622094947659445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37750130829081396631772963 56625196243622094947659445)
          ·
            refine ⟨5308612147839571401343073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 56625196243622094947659445 5308612147839571401343073)
            ·
              refine ⟨3981459110879678551007305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5308612147839571401343073 3981459110879678551007305)
              ·
                refine ⟨2986094333159758913255479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981459110879678551007305 2986094333159758913255479)
                ·
                  refine ⟨4479141499739638369883219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986094333159758913255479 4479141499739638369883219)
                  ·
                    refine ⟨6718712249609457554824829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479141499739638369883219 6718712249609457554824829)
                    ·
                      refine ⟨2519517093603546583059311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718712249609457554824829 2519517093603546583059311)
                      ·
                        rfl

theorem cell23_4906742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3].length) (baseStart_4906742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906742 prefixEnd_4906742 := by exact prefixLift 4906742
  have htrace : WordTrace (prefixWord ++ tailWord_4906742) baseStart_4906742 baseEnd_4906742 := by
    simpa [prefixWord, tailWord_4906742, baseEnd_4906742] using wordTrace_append hprefix tailTrace_4906742
  have hstable : (prefixWord ++ tailWord_4906742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906742).length < 2 ^ (prefixWord ++ tailWord_4906742).sum := by decide
  have hdescent : baseEnd_4906742 < baseStart_4906742 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906764 : List Nat := [2, 2, 1, 2, 2, 1, 3, 3, 1, 3, 3]
def baseStart_4906764 : Nat := 118140960795 + 4906764 * 2 ^ 59
def prefixEnd_4906764 : Nat := 4983230072969 + 3 ^ 40 * 4906764 * 2
def baseEnd_4906764 : Nat := 2519528390177945496984209

theorem tailTrace_4906764 : CollatzResearch.WordTrace tailWord_4906764 prefixEnd_4906764 2519528390177945496984209 := by
  unfold tailWord_4906764
  simp only [CollatzResearch.WordTrace]
  refine ⟨89482192797819755709519673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119309590397093007612692897 89482192797819755709519673)
  ·
    refine ⟨67111644598364816782139755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89482192797819755709519673 67111644598364816782139755)
    ·
      refine ⟨100667466897547225173209633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67111644598364816782139755 100667466897547225173209633)
      ·
        refine ⟨75500600173160418879907225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100667466897547225173209633 75500600173160418879907225)
        ·
          refine ⟨56625450129870314159930419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75500600173160418879907225 56625450129870314159930419)
          ·
            refine ⟨84938175194805471239895629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56625450129870314159930419 84938175194805471239895629)
            ·
              refine ⟨31851815698052051714960861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84938175194805471239895629 31851815698052051714960861)
              ·
                refine ⟨11944430886769519393110323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31851815698052051714960861 11944430886769519393110323)
                ·
                  refine ⟨17916646330154279089665485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11944430886769519393110323 17916646330154279089665485)
                  ·
                    refine ⟨6718742373807854658624557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17916646330154279089665485 6718742373807854658624557)
                    ·
                      refine ⟨2519528390177945496984209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718742373807854658624557 2519528390177945496984209)
                      ·
                        rfl

theorem cell23_4906764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_4906764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906764 prefixEnd_4906764 := by exact prefixLift 4906764
  have htrace : WordTrace (prefixWord ++ tailWord_4906764) baseStart_4906764 baseEnd_4906764 := by
    simpa [prefixWord, tailWord_4906764, baseEnd_4906764] using wordTrace_append hprefix tailTrace_4906764
  have hstable : (prefixWord ++ tailWord_4906764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906764).length < 2 ^ (prefixWord ++ tailWord_4906764).sum := by decide
  have hdescent : baseEnd_4906764 < baseStart_4906764 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906807 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5]
def baseStart_4906807 : Nat := 118140960795 + 4906807 * 2 ^ 59
def prefixEnd_4906807 : Nat := 4983230072969 + 3 ^ 40 * 4906807 * 2
def baseEnd_4906807 : Nat := 2519550469846088828746511

theorem tailTrace_4906807 : CollatzResearch.WordTrace tailWord_4906807 prefixEnd_4906807 2519550469846088828746511 := by
  unfold tailWord_4906807
  simp only [CollatzResearch.WordTrace]
  refine ⟨178965953934483729762854675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119310635956322486508569783 178965953934483729762854675)
  ·
    refine ⟨268448930901725594644282013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178965953934483729762854675 268448930901725594644282013)
    ·
      refine ⟨100668349088147097991605755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268448930901725594644282013 100668349088147097991605755)
      ·
        refine ⟨151002523632220646987408633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100668349088147097991605755 151002523632220646987408633)
        ·
          refine ⟨113251892724165485240556475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151002523632220646987408633 113251892724165485240556475)
          ·
            refine ⟨169877839086248227860834713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113251892724165485240556475 169877839086248227860834713)
            ·
              refine ⟨127408379314686170895626035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169877839086248227860834713 127408379314686170895626035)
              ·
                refine ⟨191112568972029256343439053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127408379314686170895626035 191112568972029256343439053)
                ·
                  refine ⟨71667213364510971128789645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191112568972029256343439053 71667213364510971128789645)
                  ·
                    refine ⟨26875205011691614173296117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 71667213364510971128789645 26875205011691614173296117)
                    ·
                      refine ⟨2519550469846088828746511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26875205011691614173296117 2519550469846088828746511)
                      ·
                        rfl

theorem cell23_4906807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 3, 3, 5].length) (baseStart_4906807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906807 prefixEnd_4906807 := by exact prefixLift 4906807
  have htrace : WordTrace (prefixWord ++ tailWord_4906807) baseStart_4906807 baseEnd_4906807 := by
    simpa [prefixWord, tailWord_4906807, baseEnd_4906807] using wordTrace_append hprefix tailTrace_4906807
  have hstable : (prefixWord ++ tailWord_4906807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906807).length < 2 ^ (prefixWord ++ tailWord_4906807).sum := by decide
  have hdescent : baseEnd_4906807 < baseStart_4906807 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906815 : List Nat := [1, 1, 2, 2, 6, 1, 3, 1, 2, 1, 3]
def baseStart_4906815 : Nat := 118140960795 + 4906815 * 2 ^ 59
def prefixEnd_4906815 : Nat := 4983230072969 + 3 ^ 40 * 4906815 * 2
def baseEnd_4906815 : Nat := 2519554577691324797446475

theorem tailTrace_4906815 : CollatzResearch.WordTrace tailWord_4906815 prefixEnd_4906815 2519554577691324797446475 := by
  unfold tailWord_4906815
  simp only [CollatzResearch.WordTrace]
  refine ⟨178966245718454747129145899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119310830478969831419430599 178966245718454747129145899)
  ·
    refine ⟨268449368577682120693718849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178966245718454747129145899 268449368577682120693718849)
    ·
      refine ⟨201337026433261590520289137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268449368577682120693718849 201337026433261590520289137)
      ·
        refine ⟨151002769824946192890216853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201337026433261590520289137 151002769824946192890216853)
        ·
          refine ⟨7078254835544352791728915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151002769824946192890216853 7078254835544352791728915)
          ·
            refine ⟨10617382253316529187593373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7078254835544352791728915 10617382253316529187593373)
            ·
              refine ⟨3981518344993698445347515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10617382253316529187593373 3981518344993698445347515)
              ·
                refine ⟨5972277517490547668021273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981518344993698445347515 5972277517490547668021273)
                ·
                  refine ⟨4479208138117910751015955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5972277517490547668021273 4479208138117910751015955)
                  ·
                    refine ⟨6718812207176866126523933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479208138117910751015955 6718812207176866126523933)
                    ·
                      refine ⟨2519554577691324797446475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6718812207176866126523933 2519554577691324797446475)
                      ·
                        rfl

theorem cell23_4906815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 6, 1, 3, 1, 2, 1, 3].length) (baseStart_4906815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906815 prefixEnd_4906815 := by exact prefixLift 4906815
  have htrace : WordTrace (prefixWord ++ tailWord_4906815) baseStart_4906815 baseEnd_4906815 := by
    simpa [prefixWord, tailWord_4906815, baseEnd_4906815] using wordTrace_append hprefix tailTrace_4906815
  have hstable : (prefixWord ++ tailWord_4906815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906815).length < 2 ^ (prefixWord ++ tailWord_4906815).sum := by decide
  have hdescent : baseEnd_4906815 < baseStart_4906815 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4906861 : List Nat := [1, 5, 1, 1, 1, 1, 2, 6, 5]
def baseStart_4906861 : Nat := 118140960795 + 4906861 * 2 ^ 59
def prefixEnd_4906861 : Nat := 4983230072969 + 3 ^ 40 * 4906861 * 2
def baseEnd_4906861 : Nat := 279953133089047957496807

theorem tailTrace_4906861 : CollatzResearch.WordTrace tailWord_4906861 prefixEnd_4906861 279953133089047957496807 := by
  unfold tailWord_4906861
  simp only [CollatzResearch.WordTrace]
  refine ⟨178967923476288096985320437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119311948984192064656880291 178967923476288096985320437)
  ·
    refine ⟨16778242825902009092373791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178967923476288096985320437 16778242825902009092373791)
    ·
      refine ⟨25167364238853013638560687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16778242825902009092373791 25167364238853013638560687)
      ·
        refine ⟨37751046358279520457841031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25167364238853013638560687 37751046358279520457841031)
        ·
          refine ⟨56626569537419280686761547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37751046358279520457841031 56626569537419280686761547)
          ·
            refine ⟨84939854306128921030142321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56626569537419280686761547 84939854306128921030142321)
            ·
              refine ⟨63704890729596690772606741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84939854306128921030142321 63704890729596690772606741)
              ·
                refine ⟨2986166752949844879965941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63704890729596690772606741 2986166752949844879965941)
                ·
                  refine ⟨279953133089047957496807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2986166752949844879965941 279953133089047957496807)
                  ·
                    rfl

theorem cell23_4906861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 2, 6, 5].length) (baseStart_4906861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4906861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4906861 prefixEnd_4906861 := by exact prefixLift 4906861
  have htrace : WordTrace (prefixWord ++ tailWord_4906861) baseStart_4906861 baseEnd_4906861 := by
    simpa [prefixWord, tailWord_4906861, baseEnd_4906861] using wordTrace_append hprefix tailTrace_4906861
  have hstable : (prefixWord ++ tailWord_4906861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4906861).length < 2 ^ (prefixWord ++ tailWord_4906861).sum := by decide
  have hdescent : baseEnd_4906861 < baseStart_4906861 := by decide
  rcases family_descends (prefixWord ++ tailWord_4906861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907029 : List Nat := [1, 3, 2, 1, 5, 1, 3, 2, 1, 1, 3]
def baseStart_4907029 : Nat := 118140960795 + 4907029 * 2 ^ 59
def prefixEnd_4907029 : Nat := 4983230072969 + 3 ^ 40 * 4907029 * 2
def baseEnd_4907029 : Nat := 2519664462551386960170491

theorem tailTrace_4907029 : CollatzResearch.WordTrace tailWord_4907029 prefixEnd_4907029 2519664462551386960170491 := by
  unfold tailWord_4907029
  simp only [CollatzResearch.WordTrace]
  refine ⟨178974050939679461677436141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119316033959786307784957427 178974050939679461677436141)
  ·
    refine ⟨67115269102379798129038553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178974050939679461677436141 67115269102379798129038553)
    ·
      refine ⟨50336451826784848596778915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67115269102379798129038553 50336451826784848596778915)
      ·
        refine ⟨75504677740177272895168373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50336451826784848596778915 75504677740177272895168373)
        ·
          refine ⟨7078563538141619333922035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75504677740177272895168373 7078563538141619333922035)
          ·
            refine ⟨10617845307212429000883053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7078563538141619333922035 10617845307212429000883053)
            ·
              refine ⟨3981691990204660875331145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10617845307212429000883053 3981691990204660875331145)
              ·
                refine ⟨2986268992653495656498359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981691990204660875331145 2986268992653495656498359)
                ·
                  refine ⟨4479403488980243484747539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986268992653495656498359 4479403488980243484747539)
                  ·
                    refine ⟨6719105233470365227121309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479403488980243484747539 6719105233470365227121309)
                    ·
                      refine ⟨2519664462551386960170491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719105233470365227121309 2519664462551386960170491)
                      ·
                        rfl

theorem cell23_4907029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 3, 2, 1, 1, 3].length) (baseStart_4907029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907029 prefixEnd_4907029 := by exact prefixLift 4907029
  have htrace : WordTrace (prefixWord ++ tailWord_4907029) baseStart_4907029 baseEnd_4907029 := by
    simpa [prefixWord, tailWord_4907029, baseEnd_4907029] using wordTrace_append hprefix tailTrace_4907029
  have hstable : (prefixWord ++ tailWord_4907029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907029).length < 2 ^ (prefixWord ++ tailWord_4907029).sum := by decide
  have hdescent : baseEnd_4907029 < baseStart_4907029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907045 : List Nat := [1, 3, 1, 2, 2, 3, 4, 1, 2, 4]
def baseStart_4907045 : Nat := 118140960795 + 4907045 * 2 ^ 59
def prefixEnd_4907045 : Nat := 4983230072969 + 3 ^ 40 * 4907045 * 2
def baseEnd_4907045 : Nat := 839890892747286299190139

theorem tailTrace_4907045 : CollatzResearch.WordTrace tailWord_4907045 prefixEnd_4907045 839890892747286299190139 := by
  unfold tailWord_4907045
  simp only [CollatzResearch.WordTrace]
  refine ⟨178974634507621496410018589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119316423005080997606679059 178974634507621496410018589)
  ·
    refine ⟨67115487940358061153756971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178974634507621496410018589 67115487940358061153756971)
    ·
      refine ⟨100673231910537091730635457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67115487940358061153756971 100673231910537091730635457)
      ·
        refine ⟨75504923932902818797976593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100673231910537091730635457 75504923932902818797976593)
        ·
          refine ⟨56628692949677114098482445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75504923932902818797976593 56628692949677114098482445)
          ·
            refine ⟨21235759856128917786930917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56628692949677114098482445 21235759856128917786930917)
            ·
              refine ⟨3981704973024172085049547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21235759856128917786930917 3981704973024172085049547)
              ·
                refine ⟨5972557459536258127574321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981704973024172085049547 5972557459536258127574321)
                ·
                  refine ⟨4479418094652193595680741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5972557459536258127574321 4479418094652193595680741)
                  ·
                    refine ⟨839890892747286299190139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479418094652193595680741 839890892747286299190139)
                    ·
                      rfl

theorem cell23_4907045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 4, 1, 2, 4].length) (baseStart_4907045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907045 prefixEnd_4907045 := by exact prefixLift 4907045
  have htrace : WordTrace (prefixWord ++ tailWord_4907045) baseStart_4907045 baseEnd_4907045 := by
    simpa [prefixWord, tailWord_4907045, baseEnd_4907045] using wordTrace_append hprefix tailTrace_4907045
  have hstable : (prefixWord ++ tailWord_4907045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907045).length < 2 ^ (prefixWord ++ tailWord_4907045).sum := by decide
  have hdescent : baseEnd_4907045 < baseStart_4907045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907068 : List Nat := [2, 2, 2, 2, 2, 1, 3, 2, 1, 3, 3]
def baseStart_4907068 : Nat := 118140960795 + 4907068 * 2 ^ 59
def prefixEnd_4907068 : Nat := 4983230072969 + 3 ^ 40 * 4907068 * 2
def baseEnd_4907068 : Nat := 2519684488296912307582811

theorem tailTrace_4907068 : CollatzResearch.WordTrace tailWord_4907068 prefixEnd_4907068 2519684488296912307582811 := by
  unfold tailWord_4907068
  simp only [CollatzResearch.WordTrace]
  refine ⟨89487736693269085669052929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119316982257692114225403905 89487736693269085669052929)
  ·
    refine ⟨67115802519951814251789697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89487736693269085669052929 67115802519951814251789697)
    ·
      refine ⟨50336851889963860688842273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67115802519951814251789697 50336851889963860688842273)
      ·
        refine ⟨37752638917472895516631705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50336851889963860688842273 37752638917472895516631705)
        ·
          refine ⟨28314479188104671637473779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37752638917472895516631705 28314479188104671637473779)
          ·
            refine ⟨42471718782157007456210669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28314479188104671637473779 42471718782157007456210669)
            ·
              refine ⟨15926894543308877796079001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42471718782157007456210669 15926894543308877796079001)
              ·
                refine ⟨11945170907481658347059251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15926894543308877796079001 11945170907481658347059251)
                ·
                  refine ⟨17917756361222487520588877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11945170907481658347059251 17917756361222487520588877)
                  ·
                    refine ⟨6719158635458432820220829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17917756361222487520588877 6719158635458432820220829)
                    ·
                      refine ⟨2519684488296912307582811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719158635458432820220829 2519684488296912307582811)
                      ·
                        rfl

theorem cell23_4907068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 2, 1, 3, 3].length) (baseStart_4907068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907068 prefixEnd_4907068 := by exact prefixLift 4907068
  have htrace : WordTrace (prefixWord ++ tailWord_4907068) baseStart_4907068 baseEnd_4907068 := by
    simpa [prefixWord, tailWord_4907068, baseEnd_4907068] using wordTrace_append hprefix tailTrace_4907068
  have hstable : (prefixWord ++ tailWord_4907068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907068).length < 2 ^ (prefixWord ++ tailWord_4907068).sum := by decide
  have hdescent : baseEnd_4907068 < baseStart_4907068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907086 : List Nat := [4, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_4907086 : Nat := 118140960795 + 4907086 * 2 ^ 59
def prefixEnd_4907086 : Nat := 4983230072969 + 3 ^ 40 * 4907086 * 2
def baseEnd_4907086 : Nat := 2519693730948693237157729

theorem tailTrace_4907086 : CollatzResearch.WordTrace tailWord_4907086 prefixEnd_4907086 2519693730948693237157729 := by
  unfold tailWord_4907086
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372016237559120051532639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119317419933648640274840741 22372016237559120051532639)
  ·
    refine ⟨33558024356338680077298959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22372016237559120051532639 33558024356338680077298959)
    ·
      refine ⟨50337036534508020115948439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33558024356338680077298959 50337036534508020115948439)
      ·
        refine ⟨75505554801762030173922659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50337036534508020115948439 75505554801762030173922659)
        ·
          refine ⟨113258332202643045260883989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75505554801762030173922659 113258332202643045260883989)
          ·
            refine ⟨5308984321998892746603937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 113258332202643045260883989 5308984321998892746603937)
            ·
              refine ⟨3981738241499169559952953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5308984321998892746603937 3981738241499169559952953)
              ·
                refine ⟨2986303681124377169964715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981738241499169559952953 2986303681124377169964715)
                ·
                  refine ⟨4479455521686565754947073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986303681124377169964715 4479455521686565754947073)
                  ·
                    refine ⟨3359591641264924316210305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4479455521686565754947073 3359591641264924316210305)
                    ·
                      refine ⟨2519693730948693237157729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359591641264924316210305 2519693730948693237157729)
                      ·
                        rfl

theorem cell23_4907086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_4907086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907086 prefixEnd_4907086 := by exact prefixLift 4907086
  have htrace : WordTrace (prefixWord ++ tailWord_4907086) baseStart_4907086 baseEnd_4907086 := by
    simpa [prefixWord, tailWord_4907086, baseEnd_4907086] using wordTrace_append hprefix tailTrace_4907086
  have hstable : (prefixWord ++ tailWord_4907086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907086).length < 2 ^ (prefixWord ++ tailWord_4907086).sum := by decide
  have hdescent : baseEnd_4907086 < baseStart_4907086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907121 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 4]
def baseStart_4907121 : Nat := 118140960795 + 4907121 * 2 ^ 59
def prefixEnd_4907121 : Nat := 4983230072969 + 3 ^ 40 * 4907121 * 2
def baseEnd_4907121 : Nat := 2519711702771600600220067

theorem tailTrace_4907121 : CollatzResearch.WordTrace tailWord_4907121 prefixEnd_4907121 2519711702771600600220067 := by
  unfold tailWord_4907121
  simp only [CollatzResearch.WordTrace]
  refine ⟨178977406455346161389785217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119318270970230774259856811 178977406455346161389785217)
  ·
    refine ⟨134233054841509621042338913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178977406455346161389785217 134233054841509621042338913)
    ·
      refine ⟨100674791131132215781754185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134233054841509621042338913 100674791131132215781754185)
      ·
        refine ⟨75506093348349161836315639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100674791131132215781754185 75506093348349161836315639)
        ·
          refine ⟨113259140022523742754473459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75506093348349161836315639 113259140022523742754473459)
          ·
            refine ⟨169888710033785614131710189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113259140022523742754473459 169888710033785614131710189)
            ·
              refine ⟨63708266262669605299391321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 169888710033785614131710189 63708266262669605299391321)
              ·
                refine ⟨47781199697002203974543491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63708266262669605299391321 47781199697002203974543491)
                ·
                  refine ⟨71671799545503305961815237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47781199697002203974543491 71671799545503305961815237)
                  ·
                    refine ⟨13438462414781869867840357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71671799545503305961815237 13438462414781869867840357)
                    ·
                      refine ⟨2519711702771600600220067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13438462414781869867840357 2519711702771600600220067)
                      ·
                        rfl

theorem cell23_4907121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 1, 4, 4].length) (baseStart_4907121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907121 prefixEnd_4907121 := by exact prefixLift 4907121
  have htrace : WordTrace (prefixWord ++ tailWord_4907121) baseStart_4907121 baseEnd_4907121 := by
    simpa [prefixWord, tailWord_4907121, baseEnd_4907121] using wordTrace_append hprefix tailTrace_4907121
  have hstable : (prefixWord ++ tailWord_4907121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907121).length < 2 ^ (prefixWord ++ tailWord_4907121).sum := by decide
  have hdescent : baseEnd_4907121 < baseStart_4907121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907129 : List Nat := [1, 2, 1, 3, 4, 3, 2, 1, 1, 3, 2]
def baseStart_4907129 : Nat := 118140960795 + 4907129 * 2 ^ 59
def prefixEnd_4907129 : Nat := 4983230072969 + 3 ^ 40 * 4907129 * 2
def baseEnd_4907129 : Nat := 2519715810616836568920031

theorem tailTrace_4907129 : CollatzResearch.WordTrace tailWord_4907129 prefixEnd_4907129 2519715810616836568920031 := by
  unfold tailWord_4907129
  simp only [CollatzResearch.WordTrace]
  refine ⟨178977698239317178756076441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119318465492878119170717627 178977698239317178756076441)
  ·
    refine ⟨134233273679487884067057331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178977698239317178756076441 134233273679487884067057331)
    ·
      refine ⟨201349910519231826100585997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134233273679487884067057331 201349910519231826100585997)
      ·
        refine ⟨75506216444711934787719749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201349910519231826100585997 75506216444711934787719749)
        ·
          refine ⟨14157415583383487772697453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 75506216444711934787719749 14157415583383487772697453)
          ·
            refine ⟨5309030843768807914761545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14157415583383487772697453 5309030843768807914761545)
            ·
              refine ⟨3981773132826605936071159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5309030843768807914761545 3981773132826605936071159)
              ·
                refine ⟨5972659699239908904106739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3981773132826605936071159 5972659699239908904106739)
                ·
                  refine ⟨8958989548859863356160109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5972659699239908904106739 8958989548859863356160109)
                  ·
                    refine ⟨3359621080822448758560041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8958989548859863356160109 3359621080822448758560041)
                    ·
                      refine ⟨2519715810616836568920031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359621080822448758560041 2519715810616836568920031)
                      ·
                        rfl

theorem cell23_4907129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 3, 2, 1, 1, 3, 2].length) (baseStart_4907129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907129 prefixEnd_4907129 := by exact prefixLift 4907129
  have htrace : WordTrace (prefixWord ++ tailWord_4907129) baseStart_4907129 baseEnd_4907129 := by
    simpa [prefixWord, tailWord_4907129, baseEnd_4907129] using wordTrace_append hprefix tailTrace_4907129
  have hstable : (prefixWord ++ tailWord_4907129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907129).length < 2 ^ (prefixWord ++ tailWord_4907129).sum := by decide
  have hdescent : baseEnd_4907129 < baseStart_4907129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907159 : List Nat := [1, 1, 3, 3, 5, 1, 1, 1, 1, 4, 2]
def baseStart_4907159 : Nat := 118140960795 + 4907159 * 2 ^ 59
def prefixEnd_4907159 : Nat := 4983230072969 + 3 ^ 40 * 4907159 * 2
def baseEnd_4907159 : Nat := 2519731215036471451544893

theorem tailTrace_4907159 : CollatzResearch.WordTrace tailWord_4907159 prefixEnd_4907159 2519731215036471451544893 := by
  unfold tailWord_4907159
  simp only [CollatzResearch.WordTrace]
  refine ⟨178978792429208493879668531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119319194952805662586445687 178978792429208493879668531)
  ·
    refine ⟨268468188643812740819502797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178978792429208493879668531 268468188643812740819502797)
    ·
      refine ⟨100675570741429777807313549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268468188643812740819502797 100675570741429777807313549)
      ·
        refine ⟨37753339028036166677742581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100675570741429777807313549 37753339028036166677742581)
        ·
          refine ⟨3539375533878390626038367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37753339028036166677742581 3539375533878390626038367)
          ·
            refine ⟨5309063300817585939057551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3539375533878390626038367 5309063300817585939057551)
            ·
              refine ⟨7963594951226378908586327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309063300817585939057551 7963594951226378908586327)
              ·
                refine ⟨11945392426839568362879491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7963594951226378908586327 11945392426839568362879491)
                ·
                  refine ⟨17918088640259352544319237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11945392426839568362879491 17918088640259352544319237)
                  ·
                    refine ⟨3359641620048628602059857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17918088640259352544319237 3359641620048628602059857)
                    ·
                      refine ⟨2519731215036471451544893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359641620048628602059857 2519731215036471451544893)
                      ·
                        rfl

theorem cell23_4907159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 5, 1, 1, 1, 1, 4, 2].length) (baseStart_4907159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907159 prefixEnd_4907159 := by exact prefixLift 4907159
  have htrace : WordTrace (prefixWord ++ tailWord_4907159) baseStart_4907159 baseEnd_4907159 := by
    simpa [prefixWord, tailWord_4907159, baseEnd_4907159] using wordTrace_append hprefix tailTrace_4907159
  have hstable : (prefixWord ++ tailWord_4907159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907159).length < 2 ^ (prefixWord ++ tailWord_4907159).sum := by decide
  have hdescent : baseEnd_4907159 < baseStart_4907159 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907171 : List Nat := [1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5]
def baseStart_4907171 : Nat := 118140960795 + 4907171 * 2 ^ 59
def prefixEnd_4907171 : Nat := 4983230072969 + 3 ^ 40 * 4907171 * 2
def baseEnd_4907171 : Nat := 2519737376804325404594837

theorem tailTrace_4907171 : CollatzResearch.WordTrace tailWord_4907171 prefixEnd_4907171 2519737376804325404594837 := by
  unfold tailWord_4907171
  simp only [CollatzResearch.WordTrace]
  refine ⟨178979230105165019929105367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119319486736776679952736911 178979230105165019929105367)
  ·
    refine ⟨268468845157747529893658051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178979230105165019929105367 268468845157747529893658051)
    ·
      refine ⟨402703267736621294840487077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268468845157747529893658051 402703267736621294840487077)
      ·
        refine ⟨75506862700616492782591327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402703267736621294840487077 75506862700616492782591327)
        ·
          refine ⟨113260294050924739173886991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75506862700616492782591327 113260294050924739173886991)
          ·
            refine ⟨169890441076387108760830487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113260294050924739173886991 169890441076387108760830487)
            ·
              refine ⟨254835661614580663141245731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169890441076387108760830487 254835661614580663141245731)
              ·
                refine ⟨382253492421870994711868597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254835661614580663141245731 382253492421870994711868597)
                ·
                  refine ⟨35836264914550405754237681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382253492421870994711868597 35836264914550405754237681)
                  ·
                    refine ⟨26877198685912804315678261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35836264914550405754237681 26877198685912804315678261)
                    ·
                      refine ⟨2519737376804325404594837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26877198685912804315678261 2519737376804325404594837)
                      ·
                        rfl

theorem cell23_4907171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 2, 5].length) (baseStart_4907171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907171 prefixEnd_4907171 := by exact prefixLift 4907171
  have htrace : WordTrace (prefixWord ++ tailWord_4907171) baseStart_4907171 baseEnd_4907171 := by
    simpa [prefixWord, tailWord_4907171, baseEnd_4907171] using wordTrace_append hprefix tailTrace_4907171
  have hstable : (prefixWord ++ tailWord_4907171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907171).length < 2 ^ (prefixWord ++ tailWord_4907171).sum := by decide
  have hdescent : baseEnd_4907171 < baseStart_4907171 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907242 : List Nat := [3, 1, 3, 1, 1, 2, 2, 5, 1, 4]
def baseStart_4907242 : Nat := 118140960795 + 4907242 * 2 ^ 59
def prefixEnd_4907242 : Nat := 4983230072969 + 3 ^ 40 * 4907242 * 2
def baseEnd_4907242 : Nat := 839924611310264875602337

theorem tailTrace_4907242 : CollatzResearch.WordTrace tailWord_4907242 prefixEnd_4907242 839924611310264875602337 := by
  unfold tailWord_4907242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44745454921976949763734995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119321213125271866036626653 44745454921976949763734995)
  ·
    refine ⟨67118182382965424645602493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44745454921976949763734995 67118182382965424645602493)
    ·
      refine ⟨25169318393612034242100935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67118182382965424645602493 25169318393612034242100935)
      ·
        refine ⟨37753977590418051363151403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25169318393612034242100935 37753977590418051363151403)
        ·
          refine ⟨56630966385627077044727105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37753977590418051363151403 56630966385627077044727105)
          ·
            refine ⟨42473224789220307783545329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56630966385627077044727105 42473224789220307783545329)
            ·
              refine ⟨31854918591915230837658997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42473224789220307783545329 31854918591915230837658997)
              ·
                refine ⟨2986398617992052891030531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31854918591915230837658997 2986398617992052891030531)
                ·
                  refine ⟨4479597926988079336545797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986398617992052891030531 4479597926988079336545797)
                  ·
                    refine ⟨839924611310264875602337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479597926988079336545797 839924611310264875602337)
                    ·
                      rfl

theorem cell23_4907242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 5, 1, 4].length) (baseStart_4907242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907242 prefixEnd_4907242 := by exact prefixLift 4907242
  have htrace : WordTrace (prefixWord ++ tailWord_4907242) baseStart_4907242 baseEnd_4907242 := by
    simpa [prefixWord, tailWord_4907242, baseEnd_4907242] using wordTrace_append hprefix tailTrace_4907242
  have hstable : (prefixWord ++ tailWord_4907242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907242).length < 2 ^ (prefixWord ++ tailWord_4907242).sum := by decide
  have hdescent : baseEnd_4907242 < baseStart_4907242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907275 : List Nat := [1, 1, 1, 1, 5, 2, 2, 2, 1, 5, 2]
def baseStart_4907275 : Nat := 118140960795 + 4907275 * 2 ^ 59
def prefixEnd_4907275 : Nat := 4983230072969 + 3 ^ 40 * 4907275 * 2
def baseEnd_4907275 : Nat := 2519790778792392997694359

theorem tailTrace_4907275 : CollatzResearch.WordTrace tailWord_4907275 prefixEnd_4907275 2519790778792392997694359 := by
  unfold tailWord_4907275
  simp only [CollatzResearch.WordTrace]
  refine ⟨178983023296788245690891279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119322015531192163793927519 178983023296788245690891279)
  ·
    refine ⟨268474534945182368536336919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178983023296788245690891279 268474534945182368536336919)
    ·
      refine ⟨402711802417773552804505379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268474534945182368536336919 402711802417773552804505379)
      ·
        refine ⟨604067703626660329206758069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402711802417773552804505379 604067703626660329206758069)
        ·
          refine ⟨56631347214999405863133569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 604067703626660329206758069 56631347214999405863133569)
          ·
            refine ⟨42473510411249554397350177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56631347214999405863133569 42473510411249554397350177)
            ·
              refine ⟨31855132808437165798012633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42473510411249554397350177 31855132808437165798012633)
              ·
                refine ⟨23891349606327874348509475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31855132808437165798012633 23891349606327874348509475)
                ·
                  refine ⟨35837024409491811522764213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23891349606327874348509475 35837024409491811522764213)
                  ·
                    refine ⟨3359721038389857330259145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35837024409491811522764213 3359721038389857330259145)
                    ·
                      refine ⟨2519790778792392997694359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359721038389857330259145 2519790778792392997694359)
                      ·
                        rfl

theorem cell23_4907275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 1, 5, 2].length) (baseStart_4907275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907275 prefixEnd_4907275 := by exact prefixLift 4907275
  have htrace : WordTrace (prefixWord ++ tailWord_4907275) baseStart_4907275 baseEnd_4907275 := by
    simpa [prefixWord, tailWord_4907275, baseEnd_4907275] using wordTrace_append hprefix tailTrace_4907275
  have hstable : (prefixWord ++ tailWord_4907275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907275).length < 2 ^ (prefixWord ++ tailWord_4907275).sum := by decide
  have hdescent : baseEnd_4907275 < baseStart_4907275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907278 : List Nat := [4, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_4907278 : Nat := 118140960795 + 4907278 * 2 ^ 59
def prefixEnd_4907278 : Nat := 4983230072969 + 3 ^ 40 * 4907278 * 2
def baseEnd_4907278 : Nat := 2519792319234356485956845

theorem tailTrace_4907278 : CollatzResearch.WordTrace tailWord_4907278 prefixEnd_4907278 2519792319234356485956845 := by
  unfold tailWord_4907278
  simp only [CollatzResearch.WordTrace]
  refine ⟨22372891589472172150406311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119322088477184918135500325 22372891589472172150406311)
  ·
    refine ⟨33559337384208258225609467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22372891589472172150406311 33559337384208258225609467)
    ·
      refine ⟨50339006076312387338414201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33559337384208258225609467 50339006076312387338414201)
      ·
        refine ⟨37754254557234290503810651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50339006076312387338414201 37754254557234290503810651)
        ·
          refine ⟨56631381835851435755715977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37754254557234290503810651 56631381835851435755715977)
          ·
            refine ⟨42473536376888576816786983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56631381835851435755715977 42473536376888576816786983)
            ·
              refine ⟨63710304565332865225180475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42473536376888576816786983 63710304565332865225180475)
              ·
                refine ⟨95565456847999297837770713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63710304565332865225180475 95565456847999297837770713)
                ·
                  refine ⟨71674092635999473378328035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95565456847999297837770713 71674092635999473378328035)
                  ·
                    refine ⟨107511138953999210067492053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71674092635999473378328035 107511138953999210067492053)
                    ·
                      refine ⟨2519792319234356485956845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107511138953999210067492053 2519792319234356485956845)
                      ·
                        rfl

theorem cell23_4907278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_4907278 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907278 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907278 prefixEnd_4907278 := by exact prefixLift 4907278
  have htrace : WordTrace (prefixWord ++ tailWord_4907278) baseStart_4907278 baseEnd_4907278 := by
    simpa [prefixWord, tailWord_4907278, baseEnd_4907278] using wordTrace_append hprefix tailTrace_4907278
  have hstable : (prefixWord ++ tailWord_4907278).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907278).length < 2 ^ (prefixWord ++ tailWord_4907278).sum := by decide
  have hdescent : baseEnd_4907278 < baseStart_4907278 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907299 : List Nat := [1, 1, 1, 4, 2, 2, 4, 3, 1, 1, 3]
def baseStart_4907299 : Nat := 118140960795 + 4907299 * 2 ^ 59
def prefixEnd_4907299 : Nat := 4983230072969 + 3 ^ 40 * 4907299 * 2
def baseEnd_4907299 : Nat := 2519803102328100903794249

theorem tailTrace_4907299 : CollatzResearch.WordTrace tailWord_4907299 prefixEnd_4907299 2519803102328100903794249 := by
  unfold tailWord_4907299
  simp only [CollatzResearch.WordTrace]
  refine ⟨178983898648701297789764951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119322599099134198526509967 178983898648701297789764951)
  ·
    refine ⟨268475847973051946684647427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178983898648701297789764951 268475847973051946684647427)
    ·
      refine ⟨402713771959577920026971141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268475847973051946684647427 402713771959577920026971141)
      ·
        refine ⟨75508832242420860005057089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 402713771959577920026971141 75508832242420860005057089)
        ·
          refine ⟨56631624181815645003792817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75508832242420860005057089 56631624181815645003792817)
          ·
            refine ⟨42473718136361733752844613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56631624181815645003792817 42473718136361733752844613)
            ·
              refine ⟨7963822150567825078658365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42473718136361733752844613 7963822150567825078658365)
              ·
                refine ⟨2986433306462934404496887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7963822150567825078658365 2986433306462934404496887)
                ·
                  refine ⟨4479649959694401606745331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986433306462934404496887 4479649959694401606745331)
                  ·
                    refine ⟨6719474939541602410117997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479649959694401606745331 6719474939541602410117997)
                    ·
                      refine ⟨2519803102328100903794249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719474939541602410117997 2519803102328100903794249)
                      ·
                        rfl

theorem cell23_4907299_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 4, 3, 1, 1, 3].length) (baseStart_4907299 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907299 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907299 prefixEnd_4907299 := by exact prefixLift 4907299
  have htrace : WordTrace (prefixWord ++ tailWord_4907299) baseStart_4907299 baseEnd_4907299 := by
    simpa [prefixWord, tailWord_4907299, baseEnd_4907299] using wordTrace_append hprefix tailTrace_4907299
  have hstable : (prefixWord ++ tailWord_4907299).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907299).length < 2 ^ (prefixWord ++ tailWord_4907299).sum := by decide
  have hdescent : baseEnd_4907299 < baseStart_4907299 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907299) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907315 : List Nat := [1, 1, 1, 2, 5, 1, 3, 1, 4, 4]
def baseStart_4907315 : Nat := 118140960795 + 4907315 * 2 ^ 59
def prefixEnd_4907315 : Nat := 4983230072969 + 3 ^ 40 * 4907315 * 2
def baseEnd_4907315 : Nat := 839937106006190947064725

theorem tailTrace_4907315 : CollatzResearch.WordTrace tailWord_4907315 prefixEnd_4907315 839937106006190947064725 := by
  unfold tailWord_4907315
  simp only [CollatzResearch.WordTrace]
  refine ⟨178984482216643332522347399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119322988144428888348231599 178984482216643332522347399)
  ·
    refine ⟨268476723324964998783521099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178984482216643332522347399 268476723324964998783521099)
    ·
      refine ⟨402715084987447498175281649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268476723324964998783521099 402715084987447498175281649)
      ·
        refine ⟨302036313740585623631461237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402715084987447498175281649 302036313740585623631461237)
        ·
          refine ⟨28315904413179902215449491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 302036313740585623631461237 28315904413179902215449491)
          ·
            refine ⟨42473856619769853323174237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28315904413179902215449491 42473856619769853323174237)
            ·
              refine ⟨15927696232413694996190339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42473856619769853323174237 15927696232413694996190339)
              ·
                refine ⟨23891544348620542494285509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15927696232413694996190339 23891544348620542494285509)
                ·
                  refine ⟨4479664565366351717678533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23891544348620542494285509 4479664565366351717678533)
                  ·
                    refine ⟨839937106006190947064725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479664565366351717678533 839937106006190947064725)
                    ·
                      rfl

theorem cell23_4907315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 1, 4, 4].length) (baseStart_4907315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907315 prefixEnd_4907315 := by exact prefixLift 4907315
  have htrace : WordTrace (prefixWord ++ tailWord_4907315) baseStart_4907315 baseEnd_4907315 := by
    simpa [prefixWord, tailWord_4907315, baseEnd_4907315] using wordTrace_append hprefix tailTrace_4907315
  have hstable : (prefixWord ++ tailWord_4907315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907315).length < 2 ^ (prefixWord ++ tailWord_4907315).sum := by decide
  have hdescent : baseEnd_4907315 < baseStart_4907315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907316 : List Nat := [2, 5, 1, 1, 1, 2, 2, 4, 1, 1, 3]
def baseStart_4907316 : Nat := 118140960795 + 4907316 * 2 ^ 59
def prefixEnd_4907316 : Nat := 4983230072969 + 3 ^ 40 * 4907316 * 2
def baseEnd_4907316 : Nat := 2519811831499227337281671

theorem tailTrace_4907316 : CollatzResearch.WordTrace tailWord_4907316 prefixEnd_4907316 2519811831499227337281671 := by
  unfold tailWord_4907316
  simp only [CollatzResearch.WordTrace]
  refine ⟨89492259344819854846566901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119323012459759806462089201 89492259344819854846566901)
  ·
    refine ⟨8389899313576861391865647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89492259344819854846566901 8389899313576861391865647)
    ·
      refine ⟨12584848970365292087798471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8389899313576861391865647 12584848970365292087798471)
      ·
        refine ⟨18877273455547938131697707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12584848970365292087798471 18877273455547938131697707)
        ·
          refine ⟨28315910183321907197546561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18877273455547938131697707 28315910183321907197546561)
          ·
            refine ⟨21236932637491430398159921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28315910183321907197546561 21236932637491430398159921)
            ·
              refine ⟨15927699478118572798619941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21236932637491430398159921 15927699478118572798619941)
              ·
                refine ⟨2986443652147232399741239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15927699478118572798619941 2986443652147232399741239)
                ·
                  refine ⟨4479665478220848599611859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986443652147232399741239 4479665478220848599611859)
                  ·
                    refine ⟨6719498217331272899417789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479665478220848599611859 6719498217331272899417789)
                    ·
                      refine ⟨2519811831499227337281671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719498217331272899417789 2519811831499227337281671)
                      ·
                        rfl

theorem cell23_4907316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 2, 4, 1, 1, 3].length) (baseStart_4907316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907316 prefixEnd_4907316 := by exact prefixLift 4907316
  have htrace : WordTrace (prefixWord ++ tailWord_4907316) baseStart_4907316 baseEnd_4907316 := by
    simpa [prefixWord, tailWord_4907316, baseEnd_4907316] using wordTrace_append hprefix tailTrace_4907316
  have hstable : (prefixWord ++ tailWord_4907316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907316).length < 2 ^ (prefixWord ++ tailWord_4907316).sum := by decide
  have hdescent : baseEnd_4907316 < baseStart_4907316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907345 : List Nat := [1, 2, 2, 1, 4, 2, 4, 7]
def baseStart_4907345 : Nat := 118140960795 + 4907345 * 2 ^ 59
def prefixEnd_4907345 : Nat := 4983230072969 + 3 ^ 40 * 4907345 * 2
def baseEnd_4907345 : Nat := 93326915645859545326631

theorem tailTrace_4907345 : CollatzResearch.WordTrace tailWord_4907345 prefixEnd_4907345 93326915645859545326631 := by
  unfold tailWord_4907345
  simp only [CollatzResearch.WordTrace]
  refine ⟨178985576406534647645939489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119323717604356431763959659 178985576406534647645939489)
  ·
    refine ⟨134239182304900985734454617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178985576406534647645939489 134239182304900985734454617)
    ·
      refine ⟨100679386728675739300840963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134239182304900985734454617 100679386728675739300840963)
      ·
        refine ⟨151019080093013608951261445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100679386728675739300840963 151019080093013608951261445)
        ·
          refine ⟨28316077517440051678361521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 151019080093013608951261445 28316077517440051678361521)
          ·
            refine ⟨21237058138080038758771141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28316077517440051678361521 21237058138080038758771141)
            ·
              refine ⟨3981948400890007267269589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21237058138080038758771141 3981948400890007267269589)
              ·
                refine ⟨93326915645859545326631, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3981948400890007267269589 93326915645859545326631)
                ·
                  rfl

theorem cell23_4907345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 4, 7].length) (baseStart_4907345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907345 prefixEnd_4907345 := by exact prefixLift 4907345
  have htrace : WordTrace (prefixWord ++ tailWord_4907345) baseStart_4907345 baseEnd_4907345 := by
    simpa [prefixWord, tailWord_4907345, baseEnd_4907345] using wordTrace_append hprefix tailTrace_4907345
  have hstable : (prefixWord ++ tailWord_4907345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907345).length < 2 ^ (prefixWord ++ tailWord_4907345).sum := by decide
  have hdescent : baseEnd_4907345 < baseStart_4907345 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907373 : List Nat := [1, 5, 1, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_4907373 : Nat := 118140960795 + 4907373 * 2 ^ 59
def prefixEnd_4907373 : Nat := 4983230072969 + 3 ^ 40 * 4907373 * 2
def baseEnd_4907373 : Nat := 2519841099896533614268909

theorem tailTrace_4907373 : CollatzResearch.WordTrace tailWord_4907373 prefixEnd_4907373 2519841099896533614268909 := by
  unfold tailWord_4907373
  simp only [CollatzResearch.WordTrace]
  refine ⟨178986597650433208427958773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119324398433622138951972515 178986597650433208427958773)
  ·
    refine ⟨16779993529728113290121135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 178986597650433208427958773 16779993529728113290121135)
    ·
      refine ⟨25169990294592169935181703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16779993529728113290121135 25169990294592169935181703)
      ·
        refine ⟨37754985441888254902772555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25169990294592169935181703 37754985441888254902772555)
        ·
          refine ⟨56632478162832382354158833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37754985441888254902772555 56632478162832382354158833)
          ·
            refine ⟨42474358622124286765619125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56632478162832382354158833 42474358622124286765619125)
            ·
              refine ⟨3981971120824151884276793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42474358622124286765619125 3981971120824151884276793)
              ·
                refine ⟨2986478340618113913207595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3981971120824151884276793 2986478340618113913207595)
                ·
                  refine ⟨4479717510927170869811393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986478340618113913207595 4479717510927170869811393)
                  ·
                    refine ⟨3359788133195378152358545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4479717510927170869811393 3359788133195378152358545)
                    ·
                      refine ⟨2519841099896533614268909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3359788133195378152358545 2519841099896533614268909)
                      ·
                        rfl

theorem cell23_4907373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_4907373 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907373 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907373 prefixEnd_4907373 := by exact prefixLift 4907373
  have htrace : WordTrace (prefixWord ++ tailWord_4907373) baseStart_4907373 baseEnd_4907373 := by
    simpa [prefixWord, tailWord_4907373, baseEnd_4907373] using wordTrace_append hprefix tailTrace_4907373
  have hstable : (prefixWord ++ tailWord_4907373).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907373).length < 2 ^ (prefixWord ++ tailWord_4907373).sum := by decide
  have hdescent : baseEnd_4907373 < baseStart_4907373 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907389 : List Nat := [1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 3]
def baseStart_4907389 : Nat := 118140960795 + 4907389 * 2 ^ 59
def prefixEnd_4907389 : Nat := 4983230072969 + 3 ^ 40 * 4907389 * 2
def baseEnd_4907389 : Nat := 2519849315587005551668835

theorem tailTrace_4907389 : CollatzResearch.WordTrace tailWord_4907389 prefixEnd_4907389 2519849315587005551668835 := by
  unfold tailWord_4907389
  simp only [CollatzResearch.WordTrace]
  refine ⟨178987181218375243160541221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119324787478916828773694147 178987181218375243160541221)
  ·
    refine ⟨33560096478445358092601479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 178987181218375243160541221 33560096478445358092601479)
    ·
      refine ⟨50340144717668037138902219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33560096478445358092601479 50340144717668037138902219)
      ·
        refine ⟨75510217076502055708353329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50340144717668037138902219 75510217076502055708353329)
        ·
          refine ⟨56632662807376541781264997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75510217076502055708353329 56632662807376541781264997)
          ·
            refine ⟨10618624276383101583987187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56632662807376541781264997 10618624276383101583987187)
            ·
              refine ⟨15927936414574652375980781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10618624276383101583987187 15927936414574652375980781)
              ·
                refine ⟨5972976155465494640992793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15927936414574652375980781 5972976155465494640992793)
                ·
                  refine ⟨4479732116599120980744595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5972976155465494640992793 4479732116599120980744595)
                  ·
                    refine ⟨6719598174898681471116893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479732116599120980744595 6719598174898681471116893)
                    ·
                      refine ⟨2519849315587005551668835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719598174898681471116893 2519849315587005551668835)
                      ·
                        rfl

theorem cell23_4907389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 1, 3, 2, 1, 3].length) (baseStart_4907389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907389 prefixEnd_4907389 := by exact prefixLift 4907389
  have htrace : WordTrace (prefixWord ++ tailWord_4907389) baseStart_4907389 baseEnd_4907389 := by
    simpa [prefixWord, tailWord_4907389, baseEnd_4907389] using wordTrace_append hprefix tailTrace_4907389
  have hstable : (prefixWord ++ tailWord_4907389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907389).length < 2 ^ (prefixWord ++ tailWord_4907389).sum := by decide
  have hdescent : baseEnd_4907389 < baseStart_4907389 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907415 : List Nat := [1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5]
def baseStart_4907415 : Nat := 118140960795 + 4907415 * 2 ^ 59
def prefixEnd_4907415 : Nat := 4983230072969 + 3 ^ 40 * 4907415 * 2
def baseEnd_4907415 : Nat := 2519862666084022449943715

theorem tailTrace_4907415 : CollatzResearch.WordTrace tailWord_4907415 prefixEnd_4907415 2519862666084022449943715 := by
  unfold tailWord_4907415
  simp only [CollatzResearch.WordTrace]
  refine ⟨178988129516281049600987699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119325419677520699733991799 178988129516281049600987699)
  ·
    refine ⟨268482194274421574401481549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178988129516281049600987699 268482194274421574401481549)
    ·
      refine ⟨100680822852908090400555581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268482194274421574401481549 100680822852908090400555581)
      ·
        refine ⟨37755308569840533900208343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100680822852908090400555581 37755308569840533900208343)
        ·
          refine ⟨56632962854760800850312515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37755308569840533900208343 56632962854760800850312515)
          ·
            refine ⟨84949444282141201275468773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56632962854760800850312515 84949444282141201275468773)
            ·
              refine ⟨15928020802901475239150395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 84949444282141201275468773 15928020802901475239150395)
              ·
                refine ⟨23892031204352212858725593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15928020802901475239150395 23892031204352212858725593)
                ·
                  refine ⟨17919023403264159644044195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23892031204352212858725593 17919023403264159644044195)
                  ·
                    refine ⟨26878535104896239466066293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17919023403264159644044195 26878535104896239466066293)
                    ·
                      refine ⟨2519862666084022449943715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26878535104896239466066293 2519862666084022449943715)
                      ·
                        rfl

theorem cell23_4907415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_4907415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907415 prefixEnd_4907415 := by exact prefixLift 4907415
  have htrace : WordTrace (prefixWord ++ tailWord_4907415) baseStart_4907415 baseEnd_4907415 := by
    simpa [prefixWord, tailWord_4907415, baseEnd_4907415] using wordTrace_append hprefix tailTrace_4907415
  have hstable : (prefixWord ++ tailWord_4907415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907415).length < 2 ^ (prefixWord ++ tailWord_4907415).sum := by decide
  have hdescent : baseEnd_4907415 < baseStart_4907415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907452 : List Nat := [2, 2, 2, 4, 1, 2, 1, 2, 7]
def baseStart_4907452 : Nat := 118140960795 + 4907452 * 2 ^ 59
def prefixEnd_4907452 : Nat := 4983230072969 + 3 ^ 40 * 4907452 * 2
def baseEnd_4907452 : Nat := 279986851652026533909005

theorem tailTrace_4907452 : CollatzResearch.WordTrace tailWord_4907452 prefixEnd_4907452 279986851652026533909005 := by
  unfold tailWord_4907452
  simp only [CollatzResearch.WordTrace]
  refine ⟨89494739508573502460042305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119326319344764669946723073 89494739508573502460042305)
  ·
    refine ⟨67121054631430126845031729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89494739508573502460042305 67121054631430126845031729)
    ·
      refine ⟨50340790973572595133773797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67121054631430126845031729 50340790973572595133773797)
      ·
        refine ⟨9438898307544861587582587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 50340790973572595133773797 9438898307544861587582587)
        ·
          refine ⟨14158347461317292381373881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9438898307544861587582587 14158347461317292381373881)
          ·
            refine ⟨10618760595987969286030411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14158347461317292381373881 10618760595987969286030411)
            ·
              refine ⟨15928140893981953929045617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10618760595987969286030411 15928140893981953929045617)
              ·
                refine ⟨11946105670486465446784213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15928140893981953929045617 11946105670486465446784213)
                ·
                  refine ⟨279986851652026533909005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11946105670486465446784213 279986851652026533909005)
                  ·
                    rfl

theorem cell23_4907452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 2, 7].length) (baseStart_4907452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907452 prefixEnd_4907452 := by exact prefixLift 4907452
  have htrace : WordTrace (prefixWord ++ tailWord_4907452) baseStart_4907452 baseEnd_4907452 := by
    simpa [prefixWord, tailWord_4907452, baseEnd_4907452] using wordTrace_append hprefix tailTrace_4907452
  have hstable : (prefixWord ++ tailWord_4907452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907452).length < 2 ^ (prefixWord ++ tailWord_4907452).sum := by decide
  have hdescent : baseEnd_4907452 < baseStart_4907452 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907502 : List Nat := [4, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_4907502 : Nat := 118140960795 + 4907502 * 2 ^ 59
def prefixEnd_4907502 : Nat := 4983230072969 + 3 ^ 40 * 4907502 * 2
def baseEnd_4907502 : Nat := 2519907338900963609555815

theorem tailTrace_4907502 : CollatzResearch.WordTrace tailWord_4907502 prefixEnd_4907502 2519907338900963609555815 := by
  unfold tailWord_4907502
  simp only [CollatzResearch.WordTrace]
  refine ⟨22373912833370732932425595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119327535111310575639603173 22373912833370732932425595)
  ·
    refine ⟨33560869250056099398638393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22373912833370732932425595 33560869250056099398638393)
    ·
      refine ⟨25170651937542074548978795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33560869250056099398638393 25170651937542074548978795)
      ·
        refine ⟨37755977906313111823468193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25170651937542074548978795 37755977906313111823468193)
        ·
          refine ⟨28316983429734833867601145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37755977906313111823468193 28316983429734833867601145)
          ·
            refine ⟨21237737572301125400700859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28316983429734833867601145 21237737572301125400700859)
            ·
              refine ⟨31856606358451688101051289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21237737572301125400700859 31856606358451688101051289)
              ·
                refine ⟨23892454768838766075788467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31856606358451688101051289 23892454768838766075788467)
                ·
                  refine ⟨35838682153258149113682701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23892454768838766075788467 35838682153258149113682701)
                  ·
                    refine ⟨13439505807471805917631013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35838682153258149113682701 13439505807471805917631013)
                    ·
                      refine ⟨2519907338900963609555815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13439505807471805917631013 2519907338900963609555815)
                      ·
                        rfl

theorem cell23_4907502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_4907502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907502 prefixEnd_4907502 := by exact prefixLift 4907502
  have htrace : WordTrace (prefixWord ++ tailWord_4907502) baseStart_4907502 baseEnd_4907502 := by
    simpa [prefixWord, tailWord_4907502, baseEnd_4907502] using wordTrace_append hprefix tailTrace_4907502
  have hstable : (prefixWord ++ tailWord_4907502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907502).length < 2 ^ (prefixWord ++ tailWord_4907502).sum := by decide
  have hdescent : baseEnd_4907502 < baseStart_4907502 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907512 : List Nat := [2, 1, 2, 1, 1, 4, 1, 4, 3, 4]
def baseStart_4907512 : Nat := 118140960795 + 4907512 * 2 ^ 59
def prefixEnd_4907512 : Nat := 4983230072969 + 3 ^ 40 * 4907512 * 2
def baseEnd_4907512 : Nat := 839970824569169523476923

theorem tailTrace_4907512 : CollatzResearch.WordTrace tailWord_4907512 prefixEnd_4907512 839970824569169523476923 := by
  unfold tailWord_4907512
  simp only [CollatzResearch.WordTrace]
  refine ⟨89495833698464817583634395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119327778264619756778179193 89495833698464817583634395)
  ·
    refine ⟨134243750547697226375451593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89495833698464817583634395 134243750547697226375451593)
    ·
      refine ⟨100682812910772919781588695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134243750547697226375451593 100682812910772919781588695)
      ·
        refine ⟨151024219366159379672383043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100682812910772919781588695 151024219366159379672383043)
        ·
          refine ⟨226536329049239069508574565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151024219366159379672383043 226536329049239069508574565)
          ·
            refine ⟨42475561696732325532857731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 226536329049239069508574565 42475561696732325532857731)
            ·
              refine ⟨63713342545098488299286597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42475561696732325532857731 63713342545098488299286597)
              ·
                refine ⟨11946251727205966556116237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63713342545098488299286597 11946251727205966556116237)
                ·
                  refine ⟨4479844397702237458543589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11946251727205966556116237 4479844397702237458543589)
                  ·
                    refine ⟨839970824569169523476923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479844397702237458543589 839970824569169523476923)
                    ·
                      rfl

theorem cell23_4907512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 1, 4, 3, 4].length) (baseStart_4907512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907512 prefixEnd_4907512 := by exact prefixLift 4907512
  have htrace : WordTrace (prefixWord ++ tailWord_4907512) baseStart_4907512 baseEnd_4907512 := by
    simpa [prefixWord, tailWord_4907512, baseEnd_4907512] using wordTrace_append hprefix tailTrace_4907512
  have hstable : (prefixWord ++ tailWord_4907512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907512).length < 2 ^ (prefixWord ++ tailWord_4907512).sum := by decide
  have hdescent : baseEnd_4907512 < baseStart_4907512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907525 : List Nat := [1, 3, 1, 1, 2, 2, 3, 2, 8]
def baseStart_4907525 : Nat := 118140960795 + 4907525 * 2 ^ 59
def prefixEnd_4907525 : Nat := 4983230072969 + 3 ^ 40 * 4907525 * 2
def baseEnd_4907525 : Nat := 279991016550668557729801

theorem tailTrace_4907525 : CollatzResearch.WordTrace tailWord_4907525 prefixEnd_4907525 279991016550668557729801 := by
  unfold tailWord_4907525
  simp only [CollatzResearch.WordTrace]
  refine ⟨178992141545882538387492029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119328094363921692258328019 178992141545882538387492029)
  ·
    refine ⟨67122053079705951895309511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 178992141545882538387492029 67122053079705951895309511)
    ·
      refine ⟨100683079619558927842964267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67122053079705951895309511 100683079619558927842964267)
      ·
        refine ⟨151024619429338391764446401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100683079619558927842964267 151024619429338391764446401)
        ·
          refine ⟨113268464572003793823334801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151024619429338391764446401 113268464572003793823334801)
          ·
            refine ⟨84951348429002845367501101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113268464572003793823334801 84951348429002845367501101)
            ·
              refine ⟨31856755660876067012812913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84951348429002845367501101 31856755660876067012812913)
              ·
                refine ⟨23892566745657050259609685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31856755660876067012812913 23892566745657050259609685)
                ·
                  refine ⟨279991016550668557729801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 23892566745657050259609685 279991016550668557729801)
                  ·
                    rfl

theorem cell23_4907525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 2, 8].length) (baseStart_4907525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907525 prefixEnd_4907525 := by exact prefixLift 4907525
  have htrace : WordTrace (prefixWord ++ tailWord_4907525) baseStart_4907525 baseEnd_4907525 := by
    simpa [prefixWord, tailWord_4907525, baseEnd_4907525] using wordTrace_append hprefix tailTrace_4907525
  have hstable : (prefixWord ++ tailWord_4907525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907525).length < 2 ^ (prefixWord ++ tailWord_4907525).sum := by decide
  have hdescent : baseEnd_4907525 < baseStart_4907525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907529 : List Nat := [1, 2, 1, 1, 3, 1, 2, 7, 1, 4]
def baseStart_4907529 : Nat := 118140960795 + 4907529 * 2 ^ 59
def prefixEnd_4907529 : Nat := 4983230072969 + 3 ^ 40 * 4907529 * 2
def baseEnd_4907529 : Nat := 839973734292878334639397

theorem tailTrace_4907529 : CollatzResearch.WordTrace tailWord_4907529 prefixEnd_4907529 839973734292878334639397 := by
  unfold tailWord_4907529
  simp only [CollatzResearch.WordTrace]
  refine ⟨178992287437868047070637641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119328191625245364713758427 178992287437868047070637641)
  ·
    refine ⟨134244215578401035302978231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178992287437868047070637641 134244215578401035302978231)
    ·
      refine ⟨201366323367601552954467347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134244215578401035302978231 201366323367601552954467347)
      ·
        refine ⟨302049485051402329431701021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201366323367601552954467347 302049485051402329431701021)
        ·
          refine ⟨113268556894275873536887883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302049485051402329431701021 113268556894275873536887883)
          ·
            refine ⟨169902835341413810305331825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113268556894275873536887883 169902835341413810305331825)
            ·
              refine ⟨127427126506060357728998869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169902835341413810305331825 127427126506060357728998869)
              ·
                refine ⟨2986573277485789634273411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 127427126506060357728998869 2986573277485789634273411)
                ·
                  refine ⟨4479859916228684451410117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986573277485789634273411 4479859916228684451410117)
                  ·
                    refine ⟨839973734292878334639397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479859916228684451410117 839973734292878334639397)
                    ·
                      rfl

theorem cell23_4907529_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 7, 1, 4].length) (baseStart_4907529 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907529 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907529 prefixEnd_4907529 := by exact prefixLift 4907529
  have htrace : WordTrace (prefixWord ++ tailWord_4907529) baseStart_4907529 baseEnd_4907529 := by
    simpa [prefixWord, tailWord_4907529, baseEnd_4907529] using wordTrace_append hprefix tailTrace_4907529
  have hstable : (prefixWord ++ tailWord_4907529).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907529).length < 2 ^ (prefixWord ++ tailWord_4907529).sum := by decide
  have hdescent : baseEnd_4907529 < baseStart_4907529 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907529) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907569 : List Nat := [1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 3]
def baseStart_4907569 : Nat := 118140960795 + 4907569 * 2 ^ 59
def prefixEnd_4907569 : Nat := 4983230072969 + 3 ^ 40 * 4907569 * 2
def baseEnd_4907569 : Nat := 2519941742104814847418007

theorem tailTrace_4907569 : CollatzResearch.WordTrace tailWord_4907569 prefixEnd_4907569 2519941742104814847418007 := by
  unfold tailWord_4907569
  simp only [CollatzResearch.WordTrace]
  refine ⟨178993746357723133902093761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119329164238482089268062507 178993746357723133902093761)
  ·
    refine ⟨134245309768292350426570321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 178993746357723133902093761 134245309768292350426570321)
    ·
      refine ⟨100683982326219262819927741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134245309768292350426570321 100683982326219262819927741)
      ·
        refine ⟨37756493372332223557472903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100683982326219262819927741 37756493372332223557472903)
        ·
          refine ⟨56634740058498335336209355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37756493372332223557472903 56634740058498335336209355)
          ·
            refine ⟨84952110087747503004314033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56634740058498335336209355 84952110087747503004314033)
            ·
              refine ⟨63714082565810627253235525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84952110087747503004314033 63714082565810627253235525)
              ·
                refine ⟨11946390481089492609981661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63714082565810627253235525 11946390481089492609981661)
                ·
                  refine ⟨4479896430408559728743123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11946390481089492609981661 4479896430408559728743123)
                  ·
                    refine ⟨6719844645612839593114685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4479896430408559728743123 6719844645612839593114685)
                    ·
                      refine ⟨2519941742104814847418007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719844645612839593114685 2519941742104814847418007)
                      ·
                        rfl

theorem cell23_4907569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 4, 3, 1, 3].length) (baseStart_4907569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907569 prefixEnd_4907569 := by exact prefixLift 4907569
  have htrace : WordTrace (prefixWord ++ tailWord_4907569) baseStart_4907569 baseEnd_4907569 := by
    simpa [prefixWord, tailWord_4907569, baseEnd_4907569] using wordTrace_append hprefix tailTrace_4907569
  have hstable : (prefixWord ++ tailWord_4907569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907569).length < 2 ^ (prefixWord ++ tailWord_4907569).sum := by decide
  have hdescent : baseEnd_4907569 < baseStart_4907569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907602 : List Nat := [3, 2, 2, 1, 2, 1, 1, 2, 3, 6]
def baseStart_4907602 : Nat := 118140960795 + 4907602 * 2 ^ 59
def prefixEnd_4907602 : Nat := 4983230072969 + 3 ^ 40 * 4907602 * 2
def baseEnd_4907602 : Nat := 839986228988804406101785

theorem tailTrace_4907602 : CollatzResearch.WordTrace tailWord_4907602 prefixEnd_4907602 839986228988804406101785 := by
  unfold tailWord_4907602
  simp only [CollatzResearch.WordTrace]
  refine ⟨44748737491650895134511265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119329966644402387025363373 44748737491650895134511265)
  ·
    refine ⟨33561553118738171350883449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44748737491650895134511265 33561553118738171350883449)
    ·
      refine ⟨25171164839053628513162587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33561553118738171350883449 25171164839053628513162587)
      ·
        refine ⟨37756747258580442769743881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25171164839053628513162587 37756747258580442769743881)
        ·
          refine ⟨28317560443935332077307911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37756747258580442769743881 28317560443935332077307911)
          ·
            refine ⟨42476340665902998115961867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28317560443935332077307911 42476340665902998115961867)
            ·
              refine ⟨63714510998854497173942801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42476340665902998115961867 63714510998854497173942801)
              ·
                refine ⟨47785883249140872880457101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63714510998854497173942801 47785883249140872880457101)
                ·
                  refine ⟨17919706218427827330171413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47785883249140872880457101 17919706218427827330171413)
                  ·
                    refine ⟨839986228988804406101785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17919706218427827330171413 839986228988804406101785)
                    ·
                      rfl

theorem cell23_4907602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_4907602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907602 prefixEnd_4907602 := by exact prefixLift 4907602
  have htrace : WordTrace (prefixWord ++ tailWord_4907602) baseStart_4907602 baseEnd_4907602 := by
    simpa [prefixWord, tailWord_4907602, baseEnd_4907602] using wordTrace_append hprefix tailTrace_4907602
  have hstable : (prefixWord ++ tailWord_4907602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907602).length < 2 ^ (prefixWord ++ tailWord_4907602).sum := by decide
  have hdescent : baseEnd_4907602 < baseStart_4907602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907619 : List Nat := [1, 1, 1, 5, 1, 2, 1, 5, 2, 4]
def baseStart_4907619 : Nat := 118140960795 + 4907619 * 2 ^ 59
def prefixEnd_4907619 : Nat := 4983230072969 + 3 ^ 40 * 4907619 * 2
def baseEnd_4907619 : Nat := 839989138712513217264259

theorem tailTrace_4907619 : CollatzResearch.WordTrace tailWord_4907619 prefixEnd_4907619 839989138712513217264259 := by
  unfold tailWord_4907619
  simp only [CollatzResearch.WordTrace]
  refine ⟨178995570007541992441413911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119330380005027994960942607 178995570007541992441413911)
  ·
    refine ⟨268493355011312988662120867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 178995570007541992441413911 268493355011312988662120867)
    ·
      refine ⟨402740032516969482993181301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268493355011312988662120867 402740032516969482993181301)
      ·
        refine ⟨37756878048465889030610747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 402740032516969482993181301 37756878048465889030610747)
        ·
          refine ⟨56635317072698833545916121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37756878048465889030610747 56635317072698833545916121)
          ·
            refine ⟨42476487804524125159437091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56635317072698833545916121 42476487804524125159437091)
            ·
              refine ⟨63714731706786187739155637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42476487804524125159437091 63714731706786187739155637)
              ·
                refine ⟨5973256097511205100545841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63714731706786187739155637 5973256097511205100545841)
                ·
                  refine ⟨4479942073133403825409381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5973256097511205100545841 4479942073133403825409381)
                  ·
                    refine ⟨839989138712513217264259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4479942073133403825409381 839989138712513217264259)
                    ·
                      rfl

theorem cell23_4907619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 5, 2, 4].length) (baseStart_4907619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907619 prefixEnd_4907619 := by exact prefixLift 4907619
  have htrace : WordTrace (prefixWord ++ tailWord_4907619) baseStart_4907619 baseEnd_4907619 := by
    simpa [prefixWord, tailWord_4907619, baseEnd_4907619] using wordTrace_append hprefix tailTrace_4907619
  have hstable : (prefixWord ++ tailWord_4907619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907619).length < 2 ^ (prefixWord ++ tailWord_4907619).sum := by decide
  have hdescent : baseEnd_4907619 < baseStart_4907619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907642 : List Nat := [3, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3]
def baseStart_4907642 : Nat := 118140960795 + 4907642 * 2 ^ 59
def prefixEnd_4907642 : Nat := 4983230072969 + 3 ^ 40 * 4907642 * 2
def baseEnd_4907642 : Nat := 2519979226192593061805171

theorem tailTrace_4907642 : CollatzResearch.WordTrace tailWord_4907642 prefixEnd_4907642 2519979226192593061805171 := by
  unfold tailWord_4907642
  simp only [CollatzResearch.WordTrace]
  refine ⟨44749102221614666842375295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119330939257639111579667453 44749102221614666842375295)
  ·
    refine ⟨67123653332422000263562943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44749102221614666842375295 67123653332422000263562943)
    ·
      refine ⟨100685479998633000395344415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67123653332422000263562943 100685479998633000395344415)
      ·
        refine ⟨151028219997949500593016623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100685479998633000395344415 151028219997949500593016623)
        ·
          refine ⟨226542329996924250889524935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151028219997949500593016623 226542329996924250889524935)
          ·
            refine ⟨339813494995386376334287403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226542329996924250889524935 339813494995386376334287403)
            ·
              refine ⟨509720242493079564501431105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339813494995386376334287403 509720242493079564501431105)
              ·
                refine ⟨382290181869809673376073329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509720242493079564501431105 382290181869809673376073329)
                ·
                  refine ⟨286717636402357255032054997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382290181869809673376073329 286717636402357255032054997)
                  ·
                    refine ⟨6719944603180248164813789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 286717636402357255032054997 6719944603180248164813789)
                    ·
                      refine ⟨2519979226192593061805171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719944603180248164813789 2519979226192593061805171)
                      ·
                        rfl

theorem cell23_4907642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 2, 2, 7, 3].length) (baseStart_4907642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907642 prefixEnd_4907642 := by exact prefixLift 4907642
  have htrace : WordTrace (prefixWord ++ tailWord_4907642) baseStart_4907642 baseEnd_4907642 := by
    simpa [prefixWord, tailWord_4907642, baseEnd_4907642] using wordTrace_append hprefix tailTrace_4907642
  have hstable : (prefixWord ++ tailWord_4907642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907642).length < 2 ^ (prefixWord ++ tailWord_4907642).sum := by decide
  have hdescent : baseEnd_4907642 < baseStart_4907642 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907676 : List Nat := [2, 2, 3, 2, 2, 1, 3, 1, 1, 3, 3]
def baseStart_4907676 : Nat := 118140960795 + 4907676 * 2 ^ 59
def prefixEnd_4907676 : Nat := 4983230072969 + 3 ^ 40 * 4907676 * 2
def baseEnd_4907676 : Nat := 2519996684534845928780015

theorem tailTrace_4907676 : CollatzResearch.WordTrace tailWord_4907676 prefixEnd_4907676 2519996684534845928780015 := by
  unfold tailWord_4907676
  simp only [CollatzResearch.WordTrace]
  refine ⟨89498824484167745588119441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119331765978890327450825921 89498824484167745588119441)
  ·
    refine ⟨67124118363125809191089581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89498824484167745588119441 67124118363125809191089581)
    ·
      refine ⟨25171544386172178446658593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67124118363125809191089581 25171544386172178446658593)
      ·
        refine ⟨18878658289629133834993945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25171544386172178446658593 18878658289629133834993945)
        ·
          refine ⟨14158993717221850376245459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18878658289629133834993945 14158993717221850376245459)
          ·
            refine ⟨21238490575832775564368189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14158993717221850376245459 21238490575832775564368189)
            ·
              refine ⟨7964433965937290836638071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21238490575832775564368189 7964433965937290836638071)
              ·
                refine ⟨11946650948905936254957107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7964433965937290836638071 11946650948905936254957107)
                ·
                  refine ⟨17919976423358904382435661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11946650948905936254957107 17919976423358904382435661)
                  ·
                    refine ⟨6719991158759589143413373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17919976423358904382435661 6719991158759589143413373)
                    ·
                      refine ⟨2519996684534845928780015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6719991158759589143413373 2519996684534845928780015)
                      ·
                        rfl

theorem cell23_4907676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 1, 1, 3, 3].length) (baseStart_4907676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907676 prefixEnd_4907676 := by exact prefixLift 4907676
  have htrace : WordTrace (prefixWord ++ tailWord_4907676) baseStart_4907676 baseEnd_4907676 := by
    simpa [prefixWord, tailWord_4907676, baseEnd_4907676] using wordTrace_append hprefix tailTrace_4907676
  have hstable : (prefixWord ++ tailWord_4907676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907676).length < 2 ^ (prefixWord ++ tailWord_4907676).sum := by decide
  have hdescent : baseEnd_4907676 < baseStart_4907676 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907694 : List Nat := [4, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_4907694 : Nat := 118140960795 + 4907694 * 2 ^ 59
def prefixEnd_4907694 : Nat := 4983230072969 + 3 ^ 40 * 4907694 * 2
def baseEnd_4907694 : Nat := 2520005927186626858354933

theorem tailTrace_4907694 : CollatzResearch.WordTrace tailWord_4907694 prefixEnd_4907694 2520005927186626858354933 := by
  unfold tailWord_4907694
  simp only [CollatzResearch.WordTrace]
  refine ⟨22374788185283785031299267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119332203654846853500262757 22374788185283785031299267)
  ·
    refine ⟨33562182277925677546948901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22374788185283785031299267 33562182277925677546948901)
    ·
      refine ⟨6292909177111064540052919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33562182277925677546948901 6292909177111064540052919)
      ·
        refine ⟨9439363765666596810079379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6292909177111064540052919 9439363765666596810079379)
        ·
          refine ⟨14159045648499895215119069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9439363765666596810079379 14159045648499895215119069)
          ·
            refine ⟨5309642118187460705669651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14159045648499895215119069 5309642118187460705669651)
            ·
              refine ⟨7964463177281191058504477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309642118187460705669651 7964463177281191058504477)
              ·
                refine ⟨2986673691480446646939179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7964463177281191058504477 2986673691480446646939179)
                ·
                  refine ⟨4480010537220669970408769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986673691480446646939179 4480010537220669970408769)
                  ·
                    refine ⟨3360007902915502477806577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480010537220669970408769 3360007902915502477806577)
                    ·
                      refine ⟨2520005927186626858354933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360007902915502477806577 2520005927186626858354933)
                      ·
                        rfl

theorem cell23_4907694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_4907694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907694 prefixEnd_4907694 := by exact prefixLift 4907694
  have htrace : WordTrace (prefixWord ++ tailWord_4907694) baseStart_4907694 baseEnd_4907694 := by
    simpa [prefixWord, tailWord_4907694, baseEnd_4907694] using wordTrace_append hprefix tailTrace_4907694
  have hstable : (prefixWord ++ tailWord_4907694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907694).length < 2 ^ (prefixWord ++ tailWord_4907694).sum := by decide
  have hdescent : baseEnd_4907694 < baseStart_4907694 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907766 : List Nat := [5, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3]
def baseStart_4907766 : Nat := 118140960795 + 4907766 * 2 ^ 59
def prefixEnd_4907766 : Nat := 4983230072969 + 3 ^ 40 * 4907766 * 2
def baseEnd_4907766 : Nat := 2520042897793750576654601

theorem tailTrace_4907766 : CollatzResearch.WordTrace tailWord_4907766 prefixEnd_4907766 2520042897793750576654601 := by
  unfold tailWord_4907766
  simp only [CollatzResearch.WordTrace]
  refine ⟨11187558221125589784188447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119333954358672957698010101 11187558221125589784188447)
  ·
    refine ⟨16781337331688384676282671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11187558221125589784188447 16781337331688384676282671)
    ·
      refine ⟨25172005997532577014424007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16781337331688384676282671 25172005997532577014424007)
      ·
        refine ⟨37758008996298865521636011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25172005997532577014424007 37758008996298865521636011)
        ·
          refine ⟨56637013494448298282454017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37758008996298865521636011 56637013494448298282454017)
          ·
            refine ⟨42477760120836223711840513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56637013494448298282454017 42477760120836223711840513)
            ·
              refine ⟨31858320090627167783880385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42477760120836223711840513 31858320090627167783880385)
              ·
                refine ⟨23893740067970375837910289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31858320090627167783880385 23893740067970375837910289)
                ·
                  refine ⟨17920305050977781878432717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23893740067970375837910289 17920305050977781878432717)
                  ·
                    refine ⟨6720114394116668204412269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17920305050977781878432717 6720114394116668204412269)
                    ·
                      refine ⟨2520042897793750576654601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720114394116668204412269 2520042897793750576654601)
                      ·
                        rfl

theorem cell23_4907766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3].length) (baseStart_4907766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907766 prefixEnd_4907766 := by exact prefixLift 4907766
  have htrace : WordTrace (prefixWord ++ tailWord_4907766) baseStart_4907766 baseEnd_4907766 := by
    simpa [prefixWord, tailWord_4907766, baseEnd_4907766] using wordTrace_append hprefix tailTrace_4907766
  have hstable : (prefixWord ++ tailWord_4907766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907766).length < 2 ^ (prefixWord ++ tailWord_4907766).sum := by decide
  have hdescent : baseEnd_4907766 < baseStart_4907766 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907816 : List Nat := [2, 1, 5, 1, 1, 1, 1, 2, 5, 4]
def baseStart_4907816 : Nat := 118140960795 + 4907816 * 2 ^ 59
def prefixEnd_4907816 : Nat := 4983230072969 + 3 ^ 40 * 4907816 * 2
def baseEnd_4907816 : Nat := 840022857275491793676457

theorem tailTrace_4907816 : CollatzResearch.WordTrace tailWord_4907816 prefixEnd_4907816 840022857275491793676457 := by
  unfold tailWord_4907816
  simp only [CollatzResearch.WordTrace]
  refine ⟨89501377593914147543167651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119335170125218863390890201 89501377593914147543167651)
  ·
    refine ⟨134252066390871221314751477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89501377593914147543167651 134252066390871221314751477)
    ·
      refine ⟨12586131224144176998257951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134252066390871221314751477 12586131224144176998257951)
      ·
        refine ⟨18879196836216265497386927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12586131224144176998257951 18879196836216265497386927)
        ·
          refine ⟨28318795254324398246080391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18879196836216265497386927 28318795254324398246080391)
          ·
            refine ⟨42478192881486597369120587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28318795254324398246080391 42478192881486597369120587)
            ·
              refine ⟨63717289322229896053680881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42478192881486597369120587 63717289322229896053680881)
              ·
                refine ⟨47787966991672422040260661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63717289322229896053680881 47787966991672422040260661)
                ·
                  refine ⟨4480121905469289566274437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47787966991672422040260661 4480121905469289566274437)
                  ·
                    refine ⟨840022857275491793676457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4480121905469289566274437 840022857275491793676457)
                    ·
                      rfl

theorem cell23_4907816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 2, 5, 4].length) (baseStart_4907816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907816 prefixEnd_4907816 := by exact prefixLift 4907816
  have htrace : WordTrace (prefixWord ++ tailWord_4907816) baseStart_4907816 baseEnd_4907816 := by
    simpa [prefixWord, tailWord_4907816, baseEnd_4907816] using wordTrace_append hprefix tailTrace_4907816
  have hstable : (prefixWord ++ tailWord_4907816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907816).length < 2 ^ (prefixWord ++ tailWord_4907816).sum := by decide
  have hdescent : baseEnd_4907816 < baseStart_4907816 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907826 : List Nat := [3, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_4907826 : Nat := 118140960795 + 4907826 * 2 ^ 59
def prefixEnd_4907826 : Nat := 4983230072969 + 3 ^ 40 * 4907826 * 2
def baseEnd_4907826 : Nat := 2520073706633020341904325

theorem tailTrace_4907826 : CollatzResearch.WordTrace tailWord_4907826 prefixEnd_4907826 2520073706633020341904325 := by
  unfold tailWord_4907826
  simp only [CollatzResearch.WordTrace]
  refine ⟨44750779979448016698549833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119335413278528044529466221 44750779979448016698549833)
  ·
    refine ⟨33563084984586012523912375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44750779979448016698549833 33563084984586012523912375)
    ·
      refine ⟨50344627476879018785868563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33563084984586012523912375 50344627476879018785868563)
      ·
        refine ⟨75516941215318528178802845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50344627476879018785868563 75516941215318528178802845)
        ·
          refine ⟨28318852955744448067051067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75516941215318528178802845 28318852955744448067051067)
          ·
            refine ⟨42478279433616672100576601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28318852955744448067051067 42478279433616672100576601)
            ·
              refine ⟨31858709575212504075432451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42478279433616672100576601 31858709575212504075432451)
              ·
                refine ⟨47788064362818756113148677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31858709575212504075432451 47788064362818756113148677)
                ·
                  refine ⟨8960262068028516771215377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47788064362818756113148677 8960262068028516771215377)
                  ·
                    refine ⟨6720196551021387578411533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8960262068028516771215377 6720196551021387578411533)
                    ·
                      refine ⟨2520073706633020341904325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720196551021387578411533 2520073706633020341904325)
                      ·
                        rfl

theorem cell23_4907826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_4907826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907826 prefixEnd_4907826 := by exact prefixLift 4907826
  have htrace : WordTrace (prefixWord ++ tailWord_4907826) baseStart_4907826 baseEnd_4907826 := by
    simpa [prefixWord, tailWord_4907826, baseEnd_4907826] using wordTrace_append hprefix tailTrace_4907826
  have hstable : (prefixWord ++ tailWord_4907826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907826).length < 2 ^ (prefixWord ++ tailWord_4907826).sum := by decide
  have hdescent : baseEnd_4907826 < baseStart_4907826 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907859 : List Nat := [1, 1, 1, 2, 1, 1, 3, 5, 3, 5]
def baseStart_4907859 : Nat := 118140960795 + 4907859 * 2 ^ 59
def prefixEnd_4907859 : Nat := 4983230072969 + 3 ^ 40 * 4907859 * 2
def baseEnd_4907859 : Nat := 840030217164872904263891

theorem tailTrace_4907859 : CollatzResearch.WordTrace tailWord_4907859 prefixEnd_4907859 840030217164872904263891 := by
  unfold tailWord_4907859
  simp only [CollatzResearch.WordTrace]
  refine ⟨179004323526672513430150631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119336215684448342286767087 179004323526672513430150631)
  ·
    refine ⟨268506485290008770145225947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179004323526672513430150631 268506485290008770145225947)
    ·
      refine ⟨402759727935013155217838921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268506485290008770145225947 402759727935013155217838921)
      ·
        refine ⟨302069795951259866413379191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402759727935013155217838921 302069795951259866413379191)
        ·
          refine ⟨453104693926889799620068787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302069795951259866413379191 453104693926889799620068787)
          ·
            refine ⟨679657040890334699430103181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453104693926889799620068787 679657040890334699430103181)
            ·
              refine ⟨254871390333875512286288693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 679657040890334699430103181 254871390333875512286288693)
              ·
                refine ⟨23894192843800829276839565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 254871390333875512286288693 23894192843800829276839565)
                ·
                  refine ⟨8960322316425310978814837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23894192843800829276839565 8960322316425310978814837)
                  ·
                    refine ⟨840030217164872904263891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8960322316425310978814837 840030217164872904263891)
                    ·
                      rfl

theorem cell23_4907859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 5, 3, 5].length) (baseStart_4907859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907859 prefixEnd_4907859 := by exact prefixLift 4907859
  have htrace : WordTrace (prefixWord ++ tailWord_4907859) baseStart_4907859 baseEnd_4907859 := by
    simpa [prefixWord, tailWord_4907859, baseEnd_4907859] using wordTrace_append hprefix tailTrace_4907859
  have hstable : (prefixWord ++ tailWord_4907859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907859).length < 2 ^ (prefixWord ++ tailWord_4907859).sum := by decide
  have hdescent : baseEnd_4907859 < baseStart_4907859 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907890 : List Nat := [3, 2, 1, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_4907890 : Nat := 118140960795 + 4907890 * 2 ^ 59
def prefixEnd_4907890 : Nat := 4983230072969 + 3 ^ 40 * 4907890 * 2
def baseEnd_4907890 : Nat := 2520106569394908091504031

theorem tailTrace_4907890 : CollatzResearch.WordTrace tailWord_4907890 prefixEnd_4907890 2520106569394908091504031 := by
  unfold tailWord_4907890
  simp only [CollatzResearch.WordTrace]
  refine ⟨44751363547390051431132281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119336969459706803816352749 44751363547390051431132281)
  ·
    refine ⟨33563522660542538573349211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44751363547390051431132281 33563522660542538573349211)
    ·
      refine ⟨50345283990813807860023817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33563522660542538573349211 50345283990813807860023817)
      ·
        refine ⟨37758962993110355895017863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50345283990813807860023817 37758962993110355895017863)
        ·
          refine ⟨56638444489665533842526795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37758962993110355895017863 56638444489665533842526795)
          ·
            refine ⟨84957666734498300763790193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56638444489665533842526795 84957666734498300763790193)
            ·
              refine ⟨63718250050873725572842645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84957666734498300763790193 63718250050873725572842645)
              ·
                refine ⟨2986792971134705886226999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 63718250050873725572842645 2986792971134705886226999)
                ·
                  refine ⟨4480189456702058829340499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986792971134705886226999 4480189456702058829340499)
                  ·
                    refine ⟨6720284185053088244010749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4480189456702058829340499 6720284185053088244010749)
                    ·
                      refine ⟨2520106569394908091504031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720284185053088244010749 2520106569394908091504031)
                      ·
                        rfl

theorem cell23_4907890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_4907890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907890 prefixEnd_4907890 := by exact prefixLift 4907890
  have htrace : WordTrace (prefixWord ++ tailWord_4907890) baseStart_4907890 baseEnd_4907890 := by
    simpa [prefixWord, tailWord_4907890, baseEnd_4907890] using wordTrace_append hprefix tailTrace_4907890
  have hstable : (prefixWord ++ tailWord_4907890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907890).length < 2 ^ (prefixWord ++ tailWord_4907890).sum := by decide
  have hdescent : baseEnd_4907890 < baseStart_4907890 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907896 : List Nat := [2, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2]
def baseStart_4907896 : Nat := 118140960795 + 4907896 * 2 ^ 59
def prefixEnd_4907896 : Nat := 4983230072969 + 3 ^ 40 * 4907896 * 2
def baseEnd_4907896 : Nat := 2520109650278835068029003

theorem tailTrace_4907896 : CollatzResearch.WordTrace tailWord_4907896 prefixEnd_4907896 2520109650278835068029003 := by
  unfold tailWord_4907896
  simp only [CollatzResearch.WordTrace]
  refine ⟨89502836513769234374623771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119337115351692312499498361 89502836513769234374623771)
  ·
    refine ⟨134254254770653851561935657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89502836513769234374623771 134254254770653851561935657)
    ·
      refine ⟨100690691077990388671451743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134254254770653851561935657 100690691077990388671451743)
      ·
        refine ⟨151036036616985583007177615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100690691077990388671451743 151036036616985583007177615)
        ·
          refine ⟨226554054925478374510766423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151036036616985583007177615 226554054925478374510766423)
          ·
            refine ⟨339831082388217561766149635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226554054925478374510766423 339831082388217561766149635)
            ·
              refine ⟨509746623582326342649224453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339831082388217561766149635 509746623582326342649224453)
              ·
                refine ⟨95577491921686189246729585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 509746623582326342649224453 95577491921686189246729585)
                ·
                  refine ⟨71683118941264641935047189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95577491921686189246729585 71683118941264641935047189)
                  ·
                    refine ⟨3360146200371780090705337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 71683118941264641935047189 3360146200371780090705337)
                    ·
                      refine ⟨2520109650278835068029003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360146200371780090705337 2520109650278835068029003)
                      ·
                        rfl

theorem cell23_4907896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 4, 2, 6, 2].length) (baseStart_4907896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907896 prefixEnd_4907896 := by exact prefixLift 4907896
  have htrace : WordTrace (prefixWord ++ tailWord_4907896) baseStart_4907896 baseEnd_4907896 := by
    simpa [prefixWord, tailWord_4907896, baseEnd_4907896] using wordTrace_append hprefix tailTrace_4907896
  have hstable : (prefixWord ++ tailWord_4907896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907896).length < 2 ^ (prefixWord ++ tailWord_4907896).sum := by decide
  have hdescent : baseEnd_4907896 < baseStart_4907896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907913 : List Nat := [1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 4]
def baseStart_4907913 : Nat := 118140960795 + 4907913 * 2 ^ 59
def prefixEnd_4907913 : Nat := 4983230072969 + 3 ^ 40 * 4907913 * 2
def baseEnd_4907913 : Nat := 2520118379449961501516425

theorem tailTrace_4907913 : CollatzResearch.WordTrace tailWord_4907913 prefixEnd_4907913 2520118379449961501516425 := by
  unfold tailWord_4907913
  simp only [CollatzResearch.WordTrace]
  refine ⟨179006293068476880652616393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119337528712317920435077595 179006293068476880652616393)
  ·
    refine ⟨134254719801357660489462295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179006293068476880652616393 134254719801357660489462295)
    ·
      refine ⟨201382079702036490734193443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134254719801357660489462295 201382079702036490734193443)
      ·
        refine ⟨302073119553054736101290165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201382079702036490734193443 302073119553054736101290165)
        ·
          refine ⟨28319354958098881509495953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 302073119553054736101290165 28319354958098881509495953)
          ·
            refine ⟨21239516218574161132121965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28319354958098881509495953 21239516218574161132121965)
            ·
              refine ⟨7964818581965310424545737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21239516218574161132121965 7964818581965310424545737)
              ·
                refine ⟨5973613936473982818409303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7964818581965310424545737 5973613936473982818409303)
                ·
                  refine ⟨8960420904710974227613955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5973613936473982818409303 8960420904710974227613955)
                  ·
                    refine ⟨13440631357066461341420933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8960420904710974227613955 13440631357066461341420933)
                    ·
                      refine ⟨2520118379449961501516425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13440631357066461341420933 2520118379449961501516425)
                      ·
                        rfl

theorem cell23_4907913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 3, 2, 1, 1, 4].length) (baseStart_4907913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907913 prefixEnd_4907913 := by exact prefixLift 4907913
  have htrace : WordTrace (prefixWord ++ tailWord_4907913) baseStart_4907913 baseEnd_4907913 := by
    simpa [prefixWord, tailWord_4907913, baseEnd_4907913] using wordTrace_append hprefix tailTrace_4907913
  have hstable : (prefixWord ++ tailWord_4907913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907913).length < 2 ^ (prefixWord ++ tailWord_4907913).sum := by decide
  have hdescent : baseEnd_4907913 < baseStart_4907913 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907953 : List Nat := [1, 2, 2, 4, 3, 2, 1, 8]
def baseStart_4907953 : Nat := 118140960795 + 4907953 * 2 ^ 59
def prefixEnd_4907953 : Nat := 4983230072969 + 3 ^ 40 * 4907953 * 2
def baseEnd_4907953 : Nat := 93338478469486716482083

theorem tailTrace_4907953 : CollatzResearch.WordTrace tailWord_4907953 prefixEnd_4907953 93338478469486716482083 := by
  unfold tailWord_4907953
  simp only [CollatzResearch.WordTrace]
  refine ⟨179007751988331967484072513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119338501325554644989381675 179007751988331967484072513)
  ·
    refine ⟨134255813991248975613054385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179007751988331967484072513 134255813991248975613054385)
    ·
      refine ⟨100691860493436731709790789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134255813991248975613054385 100691860493436731709790789)
      ·
        refine ⟨18879723842519387195585773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100691860493436731709790789 18879723842519387195585773)
        ·
          refine ⟨7079896440944770198344665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18879723842519387195585773 7079896440944770198344665)
          ·
            refine ⟨5309922330708577648758499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7079896440944770198344665 5309922330708577648758499)
            ·
              refine ⟨7964883496062866473137749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5309922330708577648758499 7964883496062866473137749)
              ·
                refine ⟨93338478469486716482083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7964883496062866473137749 93338478469486716482083)
                ·
                  rfl

theorem cell23_4907953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 3, 2, 1, 8].length) (baseStart_4907953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907953 prefixEnd_4907953 := by exact prefixLift 4907953
  have htrace : WordTrace (prefixWord ++ tailWord_4907953) baseStart_4907953 baseEnd_4907953 := by
    simpa [prefixWord, tailWord_4907953, baseEnd_4907953] using wordTrace_append hprefix tailTrace_4907953
  have hstable : (prefixWord ++ tailWord_4907953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907953).length < 2 ^ (prefixWord ++ tailWord_4907953).sum := by decide
  have hdescent : baseEnd_4907953 < baseStart_4907953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907966 : List Nat := [4, 2, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_4907966 : Nat := 118140960795 + 4907966 * 2 ^ 59
def prefixEnd_4907966 : Nat := 4983230072969 + 3 ^ 40 * 4907966 * 2
def baseEnd_4907966 : Nat := 840048531308216598051227

theorem tailTrace_4907966 : CollatzResearch.WordTrace tailWord_4907966 prefixEnd_4907966 840048531308216598051227 := by
  unfold tailWord_4907966
  simp only [CollatzResearch.WordTrace]
  refine ⟨22376028267160608838036969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119338817424856580469530501 22376028267160608838036969)
  ·
    refine ⟨16782021200370456628527727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22376028267160608838036969 16782021200370456628527727)
    ·
      refine ⟨25173031800555684942791591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16782021200370456628527727 25173031800555684942791591)
      ·
        refine ⟨37759547700833527414187387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25173031800555684942791591 37759547700833527414187387)
        ·
          refine ⟨56639321551250291121281081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37759547700833527414187387 56639321551250291121281081)
          ·
            refine ⟨42479491163437718340960811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56639321551250291121281081 42479491163437718340960811)
            ·
              refine ⟨63719236745156577511441217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42479491163437718340960811 63719236745156577511441217)
              ·
                refine ⟨47789427558867433133580913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63719236745156577511441217 47789427558867433133580913)
                ·
                  refine ⟨35842070669150574850185685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47789427558867433133580913 35842070669150574850185685)
                  ·
                    refine ⟨840048531308216598051227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35842070669150574850185685 840048531308216598051227)
                    ·
                      rfl

theorem cell23_4907966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_4907966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907966 prefixEnd_4907966 := by exact prefixLift 4907966
  have htrace : WordTrace (prefixWord ++ tailWord_4907966) baseStart_4907966 baseEnd_4907966 := by
    simpa [prefixWord, tailWord_4907966, baseEnd_4907966] using wordTrace_append hprefix tailTrace_4907966
  have hstable : (prefixWord ++ tailWord_4907966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907966).length < 2 ^ (prefixWord ++ tailWord_4907966).sum := by decide
  have hdescent : baseEnd_4907966 < baseStart_4907966 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4907997 : List Nat := [1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 3]
def baseStart_4907997 : Nat := 118140960795 + 4907997 * 2 ^ 59
def prefixEnd_4907997 : Nat := 4983230072969 + 3 ^ 40 * 4907997 * 2
def baseEnd_4907997 : Nat := 2520161511824939172866039

theorem tailTrace_4907997 : CollatzResearch.WordTrace tailWord_4907997 prefixEnd_4907997 2520161511824939172866039 := by
  unfold tailWord_4907997
  simp only [CollatzResearch.WordTrace]
  refine ⟨179009356800172562998674245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119339571200115041999116163 179009356800172562998674245)
  ·
    refine ⟨33564254400032355562251421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179009356800172562998674245 33564254400032355562251421)
    ·
      refine ⟨12586595400012133335844283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33564254400032355562251421 12586595400012133335844283)
      ·
        refine ⟨18879893100018200003766425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12586595400012133335844283 18879893100018200003766425)
        ·
          refine ⟨14159919825013650002824819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18879893100018200003766425 14159919825013650002824819)
          ·
            refine ⟨21239879737520475004237229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14159919825013650002824819 21239879737520475004237229)
            ·
              refine ⟨7964954901570178126588961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21239879737520475004237229 7964954901570178126588961)
              ·
                refine ⟨5973716176177633594941721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7964954901570178126588961 5973716176177633594941721)
                ·
                  refine ⟨4480287132133225196206291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5973716176177633594941721 4480287132133225196206291)
                  ·
                    refine ⟨6720430698199837794309437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4480287132133225196206291 6720430698199837794309437)
                    ·
                      refine ⟨2520161511824939172866039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720430698199837794309437 2520161511824939172866039)
                      ·
                        rfl

theorem cell23_4907997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 3, 2, 2, 1, 3].length) (baseStart_4907997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4907997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4907997 prefixEnd_4907997 := by exact prefixLift 4907997
  have htrace : WordTrace (prefixWord ++ tailWord_4907997) baseStart_4907997 baseEnd_4907997 := by
    simpa [prefixWord, tailWord_4907997, baseEnd_4907997] using wordTrace_append hprefix tailTrace_4907997
  have hstable : (prefixWord ++ tailWord_4907997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4907997).length < 2 ^ (prefixWord ++ tailWord_4907997).sum := by decide
  have hdescent : baseEnd_4907997 < baseStart_4907997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4907997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908014 : List Nat := [4, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_4908014 : Nat := 118140960795 + 4908014 * 2 ^ 59
def prefixEnd_4908014 : Nat := 4983230072969 + 3 ^ 40 * 4908014 * 2
def baseEnd_4908014 : Nat := 2520170240996065606353461

theorem tailTrace_4908014 : CollatzResearch.WordTrace tailWord_4908014 prefixEnd_4908014 2520170240996065606353461 := by
  unfold tailWord_4908014
  simp only [CollatzResearch.WordTrace]
  refine ⟨22376247105138871862755387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119339984560740649934695397 22376247105138871862755387)
  ·
    refine ⟨33564370657708307794133081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22376247105138871862755387 33564370657708307794133081)
    ·
      refine ⟨25173277993281230845599811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33564370657708307794133081 25173277993281230845599811)
      ·
        refine ⟨37759916989921846268399717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25173277993281230845599811 37759916989921846268399717)
        ·
          refine ⟨7079984435610346175324947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37759916989921846268399717 7079984435610346175324947)
          ·
            refine ⟨10619976653415519262987421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7079984435610346175324947 10619976653415519262987421)
            ·
              refine ⟨3982491245030819723620283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10619976653415519262987421 3982491245030819723620283)
              ·
                refine ⟨5973736867546229585430425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982491245030819723620283 5973736867546229585430425)
                ·
                  refine ⟨4480302650659672189072819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5973736867546229585430425 4480302650659672189072819)
                  ·
                    refine ⟨6720453975989508283609229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4480302650659672189072819 6720453975989508283609229)
                    ·
                      refine ⟨2520170240996065606353461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720453975989508283609229 2520170240996065606353461)
                      ·
                        rfl

theorem cell23_4908014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_4908014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908014 prefixEnd_4908014 := by exact prefixLift 4908014
  have htrace : WordTrace (prefixWord ++ tailWord_4908014) baseStart_4908014 baseEnd_4908014 := by
    simpa [prefixWord, tailWord_4908014, baseEnd_4908014] using wordTrace_append hprefix tailTrace_4908014
  have hstable : (prefixWord ++ tailWord_4908014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908014).length < 2 ^ (prefixWord ++ tailWord_4908014).sum := by decide
  have hdescent : baseEnd_4908014 < baseStart_4908014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908060 : List Nat := [2, 2, 3, 1, 4, 2, 1, 1, 7]
def baseStart_4908060 : Nat := 118140960795 + 4908060 * 2 ^ 59
def prefixEnd_4908060 : Nat := 4983230072969 + 3 ^ 40 * 4908060 * 2
def baseEnd_4908060 : Nat := 280021540122908047375361

theorem tailTrace_4908060 : CollatzResearch.WordTrace tailWord_4908060 prefixEnd_4908060 280021540122908047375361 := by
  unfold tailWord_4908060
  simp only [CollatzResearch.WordTrace]
  refine ⟨89505827299472162379108817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119341103065962883172145089 89505827299472162379108817)
  ·
    refine ⟨67129370474604121784331613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89505827299472162379108817 67129370474604121784331613)
    ·
      refine ⟨25173513927976545669124355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67129370474604121784331613 25173513927976545669124355)
      ·
        refine ⟨37760270891964818503686533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25173513927976545669124355 37760270891964818503686533)
        ·
          refine ⟨7080050792243403469441225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37760270891964818503686533 7080050792243403469441225)
          ·
            refine ⟨5310038094182552602080919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080050792243403469441225 5310038094182552602080919)
            ·
              refine ⟨7965057141273828903121379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310038094182552602080919 7965057141273828903121379)
              ·
                refine ⟨11947585711910743354682069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965057141273828903121379 11947585711910743354682069)
                ·
                  refine ⟨280021540122908047375361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11947585711910743354682069 280021540122908047375361)
                  ·
                    rfl

theorem cell23_4908060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 4, 2, 1, 1, 7].length) (baseStart_4908060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908060 prefixEnd_4908060 := by exact prefixLift 4908060
  have htrace : WordTrace (prefixWord ++ tailWord_4908060) baseStart_4908060 baseEnd_4908060 := by
    simpa [prefixWord, tailWord_4908060, baseEnd_4908060] using wordTrace_append hprefix tailTrace_4908060
  have hstable : (prefixWord ++ tailWord_4908060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908060).length < 2 ^ (prefixWord ++ tailWord_4908060).sum := by decide
  have hdescent : baseEnd_4908060 < baseStart_4908060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908071 : List Nat := [1, 1, 7, 1, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4908071 : Nat := 118140960795 + 4908071 * 2 ^ 59
def prefixEnd_4908071 : Nat := 4983230072969 + 3 ^ 40 * 4908071 * 2
def baseEnd_4908071 : Nat := 2520199509393371883340699

theorem tailTrace_4908071 : CollatzResearch.WordTrace tailWord_4908071 prefixEnd_4908071 2520199509393371883340699 := by
  unfold tailWord_4908071
  simp only [CollatzResearch.WordTrace]
  refine ⟨179012055801904473636868067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119341370534602982424578711 179012055801904473636868067)
  ·
    refine ⟨268518083702856710455302101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179012055801904473636868067 268518083702856710455302101)
    ·
      refine ⟨6293392586785704151296143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 268518083702856710455302101 6293392586785704151296143)
      ·
        refine ⟨9440088880178556226944215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6293392586785704151296143 9440088880178556226944215)
        ·
          refine ⟨14160133320267834340416323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440088880178556226944215 14160133320267834340416323)
          ·
            refine ⟨21240199980401751510624485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160133320267834340416323 21240199980401751510624485)
            ·
              refine ⟨3982537496325328408242091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21240199980401751510624485 3982537496325328408242091)
              ·
                refine ⟨5973806244487992612363137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982537496325328408242091 5973806244487992612363137)
                ·
                  refine ⟨4480354683365994459272353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5973806244487992612363137 4480354683365994459272353)
                  ·
                    refine ⟨3360266012524495844454265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480354683365994459272353 3360266012524495844454265)
                    ·
                      refine ⟨2520199509393371883340699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360266012524495844454265 2520199509393371883340699)
                      ·
                        rfl

theorem cell23_4908071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4908071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908071 prefixEnd_4908071 := by exact prefixLift 4908071
  have htrace : WordTrace (prefixWord ++ tailWord_4908071) baseStart_4908071 baseEnd_4908071 := by
    simpa [prefixWord, tailWord_4908071, baseEnd_4908071] using wordTrace_append hprefix tailTrace_4908071
  have hstable : (prefixWord ++ tailWord_4908071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908071).length < 2 ^ (prefixWord ++ tailWord_4908071).sum := by decide
  have hdescent : baseEnd_4908071 < baseStart_4908071 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908110 : List Nat := [4, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_4908110 : Nat := 118140960795 + 4908110 * 2 ^ 59
def prefixEnd_4908110 : Nat := 4983230072969 + 3 ^ 40 * 4908110 * 2
def baseEnd_4908110 : Nat := 2520219535138897230753019

theorem tailTrace_4908110 : CollatzResearch.WordTrace tailWord_4908110 prefixEnd_4908110 2520219535138897230753019 := by
  unfold tailWord_4908110
  simp only [CollatzResearch.WordTrace]
  refine ⟨22376684781095397912192223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119342318832508788865025189 22376684781095397912192223)
  ·
    refine ⟨33565027171643096868288335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22376684781095397912192223 33565027171643096868288335)
    ·
      refine ⟨50347540757464645302432503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33565027171643096868288335 50347540757464645302432503)
      ·
        refine ⟨75521311136196967953648755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50347540757464645302432503 75521311136196967953648755)
        ·
          refine ⟨113281966704295451930473133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75521311136196967953648755 113281966704295451930473133)
          ·
            refine ⟨42480737514110794473927425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113281966704295451930473133 42480737514110794473927425)
            ·
              refine ⟨31860553135583095855445569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42480737514110794473927425 31860553135583095855445569)
              ·
                refine ⟨23895414851687321891584177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31860553135583095855445569 23895414851687321891584177)
                ·
                  refine ⟨17921561138765491418688133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23895414851687321891584177 17921561138765491418688133)
                  ·
                    refine ⟨3360292713518529641004025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17921561138765491418688133 3360292713518529641004025)
                    ·
                      refine ⟨2520219535138897230753019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360292713518529641004025 2520219535138897230753019)
                      ·
                        rfl

theorem cell23_4908110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_4908110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908110 prefixEnd_4908110 := by exact prefixLift 4908110
  have htrace : WordTrace (prefixWord ++ tailWord_4908110) baseStart_4908110 baseEnd_4908110 := by
    simpa [prefixWord, tailWord_4908110, baseEnd_4908110] using wordTrace_append hprefix tailTrace_4908110
  have hstable : (prefixWord ++ tailWord_4908110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908110).length < 2 ^ (prefixWord ++ tailWord_4908110).sum := by decide
  have hdescent : baseEnd_4908110 < baseStart_4908110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908133 : List Nat := [1, 3, 1, 3, 2, 1, 1, 5, 6]
def baseStart_4908133 : Nat := 118140960795 + 4908133 * 2 ^ 59
def prefixEnd_4908133 : Nat := 4983230072969 + 3 ^ 40 * 4908133 * 2
def baseEnd_4908133 : Nat := 280025705021550071196157

theorem tailTrace_4908133 : CollatzResearch.WordTrace tailWord_4908133 prefixEnd_4908133 280025705021550071196157 := by
  unfold tailWord_4908133
  simp only [CollatzResearch.WordTrace]
  refine ⟨179014317127679858225625053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119342878085119905483750035 179014317127679858225625053)
  ·
    refine ⟨67130368922879946834609395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179014317127679858225625053 67130368922879946834609395)
    ·
      refine ⟨100695553384319920251914093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67130368922879946834609395 100695553384319920251914093)
      ·
        refine ⟨37760832519119970094467785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100695553384319920251914093 37760832519119970094467785)
        ·
          refine ⟨28320624389339977570850839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37760832519119970094467785 28320624389339977570850839)
          ·
            refine ⟨42480936584009966356276259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28320624389339977570850839 42480936584009966356276259)
            ·
              refine ⟨63721404876014949534414389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42480936584009966356276259 63721404876014949534414389)
              ·
                refine ⟨5973881707126401518851349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63721404876014949534414389 5973881707126401518851349)
                ·
                  refine ⟨280025705021550071196157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5973881707126401518851349 280025705021550071196157)
                  ·
                    rfl

theorem cell23_4908133_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 5, 6].length) (baseStart_4908133 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908133 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908133 prefixEnd_4908133 := by exact prefixLift 4908133
  have htrace : WordTrace (prefixWord ++ tailWord_4908133) baseStart_4908133 baseEnd_4908133 := by
    simpa [prefixWord, tailWord_4908133, baseEnd_4908133] using wordTrace_append hprefix tailTrace_4908133
  have hstable : (prefixWord ++ tailWord_4908133).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908133).length < 2 ^ (prefixWord ++ tailWord_4908133).sum := by decide
  have hdescent : baseEnd_4908133 < baseStart_4908133 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908133) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908210 : List Nat := [3, 2, 1, 1, 1, 4, 1, 2, 4, 4]
def baseStart_4908210 : Nat := 118140960795 + 4908210 * 2 ^ 59
def prefixEnd_4908210 : Nat := 4983230072969 + 3 ^ 40 * 4908210 * 2
def baseEnd_4908210 : Nat := 840090294401448946500853

theorem tailTrace_4908210 : CollatzResearch.WordTrace tailWord_4908210 prefixEnd_4908210 840090294401448946500853 := by
  unfold tailWord_4908210
  simp only [CollatzResearch.WordTrace]
  refine ⟨44754281387100225094044521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119344750365600600250785389 44754281387100225094044521)
  ·
    refine ⟨33565711040325168820533391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44754281387100225094044521 33565711040325168820533391)
    ·
      refine ⟨50348566560487753230800087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33565711040325168820533391 50348566560487753230800087)
      ·
        refine ⟨75522849840731629846200131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50348566560487753230800087 75522849840731629846200131)
        ·
          refine ⟨113284274761097444769300197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75522849840731629846200131 113284274761097444769300197)
          ·
            refine ⟨21240801517705770894243787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113284274761097444769300197 21240801517705770894243787)
            ·
              refine ⟨31861202276558656341365681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21240801517705770894243787 31861202276558656341365681)
              ·
                refine ⟨23895901707418992256024261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31861202276558656341365681 23895901707418992256024261)
                ·
                  refine ⟨4480481570141061048004549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23895901707418992256024261 4480481570141061048004549)
                  ·
                    refine ⟨840090294401448946500853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4480481570141061048004549 840090294401448946500853)
                    ·
                      rfl

theorem cell23_4908210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_4908210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908210 prefixEnd_4908210 := by exact prefixLift 4908210
  have htrace : WordTrace (prefixWord ++ tailWord_4908210) baseStart_4908210 baseEnd_4908210 := by
    simpa [prefixWord, tailWord_4908210, baseEnd_4908210] using wordTrace_append hprefix tailTrace_4908210
  have hstable : (prefixWord ++ tailWord_4908210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908210).length < 2 ^ (prefixWord ++ tailWord_4908210).sum := by decide
  have hdescent : baseEnd_4908210 < baseStart_4908210 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908220 : List Nat := [2, 2, 2, 3, 2, 1, 1, 3, 1, 1, 5]
def baseStart_4908220 : Nat := 118140960795 + 4908220 * 2 ^ 59
def prefixEnd_4908220 : Nat := 4983230072969 + 3 ^ 40 * 4908220 * 2
def baseEnd_4908220 : Nat := 2520276018010891800377513

theorem tailTrace_4908220 : CollatzResearch.WordTrace tailWord_4908220 prefixEnd_4908220 2520276018010891800377513 := by
  unfold tailWord_4908220
  simp only [CollatzResearch.WordTrace]
  refine ⟨89508745139182336042021057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119344993518909781389361409 89508745139182336042021057)
  ·
    refine ⟨67131558854386752031515793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89508745139182336042021057 67131558854386752031515793)
    ·
      refine ⟨50348669140790064023636845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67131558854386752031515793 50348669140790064023636845)
      ·
        refine ⟨18880750927796274008863817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50348669140790064023636845 18880750927796274008863817)
        ·
          refine ⟨14160563195847205506647863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18880750927796274008863817 14160563195847205506647863)
          ·
            refine ⟨21240844793770808259971795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14160563195847205506647863 21240844793770808259971795)
            ·
              refine ⟨31861267190656212389957693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21240844793770808259971795 31861267190656212389957693)
              ·
                refine ⟨11947975196496079646234135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31861267190656212389957693 11947975196496079646234135)
                ·
                  refine ⟨17921962794744119469351203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11947975196496079646234135 17921962794744119469351203)
                  ·
                    refine ⟨26882944192116179204026805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17921962794744119469351203 26882944192116179204026805)
                    ·
                      refine ⟨2520276018010891800377513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26882944192116179204026805 2520276018010891800377513)
                      ·
                        rfl

theorem cell23_4908220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_4908220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908220 prefixEnd_4908220 := by exact prefixLift 4908220
  have htrace : WordTrace (prefixWord ++ tailWord_4908220) baseStart_4908220 baseEnd_4908220 := by
    simpa [prefixWord, tailWord_4908220, baseEnd_4908220] using wordTrace_append hprefix tailTrace_4908220
  have hstable : (prefixWord ++ tailWord_4908220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908220).length < 2 ^ (prefixWord ++ tailWord_4908220).sum := by decide
  have hdescent : baseEnd_4908220 < baseStart_4908220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908228 : List Nat := [2, 3, 3, 1, 3, 1, 3, 2, 1, 1, 3]
def baseStart_4908228 : Nat := 118140960795 + 4908228 * 2 ^ 59
def prefixEnd_4908228 : Nat := 4983230072969 + 3 ^ 40 * 4908228 * 2
def baseEnd_4908228 : Nat := 2520280125856127769077477

theorem tailTrace_4908228 : CollatzResearch.WordTrace tailWord_4908228 prefixEnd_4908228 2520280125856127769077477 := by
  unfold tailWord_4908228
  simp only [CollatzResearch.WordTrace]
  refine ⟨89508891031167844725166669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119345188041557126300222225 89508891031167844725166669)
  ·
    refine ⟨33565834136687941771937501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89508891031167844725166669 33565834136687941771937501)
    ·
      refine ⟨12587187801257978164476563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33565834136687941771937501 12587187801257978164476563)
      ·
        refine ⟨18880781701886967246714845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12587187801257978164476563 18880781701886967246714845)
        ·
          refine ⟨7080293138207612717518067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18880781701886967246714845 7080293138207612717518067)
          ·
            refine ⟨10620439707311419076277101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080293138207612717518067 10620439707311419076277101)
            ·
              refine ⟨3982664890241782153603913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10620439707311419076277101 3982664890241782153603913)
              ·
                refine ⟨2986998667681336615202935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982664890241782153603913 2986998667681336615202935)
                ·
                  refine ⟨4480498001522004922804403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2986998667681336615202935 4480498001522004922804403)
                  ·
                    refine ⟨6720747002283007384206605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4480498001522004922804403 6720747002283007384206605)
                    ·
                      refine ⟨2520280125856127769077477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720747002283007384206605 2520280125856127769077477)
                      ·
                        rfl

theorem cell23_4908228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 3, 2, 1, 1, 3].length) (baseStart_4908228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908228 prefixEnd_4908228 := by exact prefixLift 4908228
  have htrace : WordTrace (prefixWord ++ tailWord_4908228) baseStart_4908228 baseEnd_4908228 := by
    simpa [prefixWord, tailWord_4908228, baseEnd_4908228] using wordTrace_append hprefix tailTrace_4908228
  have hstable : (prefixWord ++ tailWord_4908228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908228).length < 2 ^ (prefixWord ++ tailWord_4908228).sum := by decide
  have hdescent : baseEnd_4908228 < baseStart_4908228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908234 : List Nat := [3, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2]
def baseStart_4908234 : Nat := 118140960795 + 4908234 * 2 ^ 59
def prefixEnd_4908234 : Nat := 4983230072969 + 3 ^ 40 * 4908234 * 2
def baseEnd_4908234 : Nat := 2520283206740054745602449

theorem tailTrace_4908234 : CollatzResearch.WordTrace tailWord_4908234 prefixEnd_4908234 2520283206740054745602449 := by
  unfold tailWord_4908234
  simp only [CollatzResearch.WordTrace]
  refine ⟨44754500225078488118762939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119345333933542634983367837 44754500225078488118762939)
  ·
    refine ⟨67131750337617732178144409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44754500225078488118762939 67131750337617732178144409)
    ·
      refine ⟨50348812753213299133608307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67131750337617732178144409 50348812753213299133608307)
      ·
        refine ⟨75523219129819948700412461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50348812753213299133608307 75523219129819948700412461)
        ·
          refine ⟨28321207173682480762654673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75523219129819948700412461 28321207173682480762654673)
          ·
            refine ⟨21240905380261860571991005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28321207173682480762654673 21240905380261860571991005)
            ·
              refine ⟨7965339517598197714496627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21240905380261860571991005 7965339517598197714496627)
              ·
                refine ⟨11948009276397296571744941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965339517598197714496627 11948009276397296571744941)
                ·
                  refine ⟨4480503478648986214404353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11948009276397296571744941 4480503478648986214404353)
                  ·
                    refine ⟨3360377608986739660803265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480503478648986214404353 3360377608986739660803265)
                    ·
                      refine ⟨2520283206740054745602449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360377608986739660803265 2520283206740054745602449)
                      ·
                        rfl

theorem cell23_4908234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_4908234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908234 prefixEnd_4908234 := by exact prefixLift 4908234
  have htrace : WordTrace (prefixWord ++ tailWord_4908234) baseStart_4908234 baseEnd_4908234 := by
    simpa [prefixWord, tailWord_4908234, baseEnd_4908234] using wordTrace_append hprefix tailTrace_4908234
  have hstable : (prefixWord ++ tailWord_4908234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908234).length < 2 ^ (prefixWord ++ tailWord_4908234).sum := by decide
  have hdescent : baseEnd_4908234 < baseStart_4908234 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908250 : List Nat := [3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3]
def baseStart_4908250 : Nat := 118140960795 + 4908250 * 2 ^ 59
def prefixEnd_4908250 : Nat := 4983230072969 + 3 ^ 40 * 4908250 * 2
def baseEnd_4908250 : Nat := 2520291422430526683002375

theorem tailTrace_4908250 : CollatzResearch.WordTrace tailWord_4908250 prefixEnd_4908250 2520291422430526683002375 := by
  unfold tailWord_4908250
  simp only [CollatzResearch.WordTrace]
  refine ⟨44754646117063996801908551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119345722978837324805089469 44754646117063996801908551)
  ·
    refine ⟨67131969175595995202862827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44754646117063996801908551 67131969175595995202862827)
    ·
      refine ⟨100697953763393992804294241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67131969175595995202862827 100697953763393992804294241)
      ·
        refine ⟨75523465322545494603220681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100697953763393992804294241 75523465322545494603220681)
        ·
          refine ⟨56642598991909120952415511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75523465322545494603220681 56642598991909120952415511)
          ·
            refine ⟨84963898487863681428623267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56642598991909120952415511 84963898487863681428623267)
            ·
              refine ⟨127445847731795522142934901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84963898487863681428623267 127445847731795522142934901)
              ·
                refine ⟨11948048224855830200900147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 127445847731795522142934901 11948048224855830200900147)
                ·
                  refine ⟨17922072337283745301350221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11948048224855830200900147 17922072337283745301350221)
                  ·
                    refine ⟨6720777126481404488006333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17922072337283745301350221 6720777126481404488006333)
                    ·
                      refine ⟨2520291422430526683002375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6720777126481404488006333 2520291422430526683002375)
                      ·
                        rfl

theorem cell23_4908250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 3].length) (baseStart_4908250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908250 prefixEnd_4908250 := by exact prefixLift 4908250
  have htrace : WordTrace (prefixWord ++ tailWord_4908250) baseStart_4908250 baseEnd_4908250 := by
    simpa [prefixWord, tailWord_4908250, baseEnd_4908250] using wordTrace_append hprefix tailTrace_4908250
  have hstable : (prefixWord ++ tailWord_4908250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908250).length < 2 ^ (prefixWord ++ tailWord_4908250).sum := by decide
  have hdescent : baseEnd_4908250 < baseStart_4908250 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908300 : List Nat := [2, 2, 1, 2, 2, 4, 1, 1, 2, 6]
def baseStart_4908300 : Nat := 118140960795 + 4908300 * 2 ^ 59
def prefixEnd_4908300 : Nat := 4983230072969 + 3 ^ 40 * 4908300 * 2
def baseEnd_4908300 : Nat := 840105698821083829125715

theorem tailTrace_4908300 : CollatzResearch.WordTrace tailWord_4908300 prefixEnd_4908300 840105698821083829125715 := by
  unfold tailWord_4908300
  simp only [CollatzResearch.WordTrace]
  refine ⟨89510204059037422873477177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119346938745383230497969569 89510204059037422873477177)
  ·
    refine ⟨67132653044278067155107883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89510204059037422873477177 67132653044278067155107883)
    ·
      refine ⟨100698979566417100732661825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67132653044278067155107883 100698979566417100732661825)
      ·
        refine ⟨75524234674812825549496369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100698979566417100732661825 75524234674812825549496369)
        ·
          refine ⟨56643176006109619162122277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75524234674812825549496369 56643176006109619162122277)
          ·
            refine ⟨10620595501145553592897927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56643176006109619162122277 10620595501145553592897927)
            ·
              refine ⟨15930893251718330389346891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10620595501145553592897927 15930893251718330389346891)
              ·
                refine ⟨23896339877577495584020337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15930893251718330389346891 23896339877577495584020337)
                ·
                  refine ⟨17922254908183121688015253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23896339877577495584020337 17922254908183121688015253)
                  ·
                    refine ⟨840105698821083829125715, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17922254908183121688015253 840105698821083829125715)
                    ·
                      rfl

theorem cell23_4908300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 1, 2, 6].length) (baseStart_4908300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908300 prefixEnd_4908300 := by exact prefixLift 4908300
  have htrace : WordTrace (prefixWord ++ tailWord_4908300) baseStart_4908300 baseEnd_4908300 := by
    simpa [prefixWord, tailWord_4908300, baseEnd_4908300] using wordTrace_append hprefix tailTrace_4908300
  have hstable : (prefixWord ++ tailWord_4908300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908300).length < 2 ^ (prefixWord ++ tailWord_4908300).sum := by decide
  have hdescent : baseEnd_4908300 < baseStart_4908300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908307 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 8, 2, 2]
def baseStart_4908307 : Nat := 118140960795 + 4908307 * 2 ^ 59
def prefixEnd_4908307 : Nat := 4983230072969 + 3 ^ 40 * 4908307 * 2
def baseEnd_4908307 : Nat := 2520320690827832959989613

theorem tailTrace_4908307 : CollatzResearch.WordTrace tailWord_4908307 prefixEnd_4908307 2520320690827832959989613 := by
  unfold tailWord_4908307
  simp only [CollatzResearch.WordTrace]
  refine ⟨179020663429049485942459175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119347108952699657294972783 179020663429049485942459175)
  ·
    refine ⟨268530995143574228913688763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179020663429049485942459175 268530995143574228913688763)
    ·
      refine ⟨402796492715361343370533145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268530995143574228913688763 402796492715361343370533145)
      ·
        refine ⟨302097369536521007527899859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402796492715361343370533145 302097369536521007527899859)
        ·
          refine ⟨453146054304781511291849789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302097369536521007527899859 453146054304781511291849789)
          ·
            refine ⟨169929770364293066734443671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 453146054304781511291849789 169929770364293066734443671)
            ·
              refine ⟨254894655546439600101665507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169929770364293066734443671 254894655546439600101665507)
              ·
                refine ⟨382341983319659400152498261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254894655546439600101665507 382341983319659400152498261)
                ·
                  refine ⟨4480570117027258595537089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 382341983319659400152498261 4480570117027258595537089)
                  ·
                    refine ⟨3360427587770443946652817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480570117027258595537089 3360427587770443946652817)
                    ·
                      refine ⟨2520320690827832959989613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360427587770443946652817 2520320690827832959989613)
                      ·
                        rfl

theorem cell23_4908307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 8, 2, 2].length) (baseStart_4908307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908307 prefixEnd_4908307 := by exact prefixLift 4908307
  have htrace : WordTrace (prefixWord ++ tailWord_4908307) baseStart_4908307 baseEnd_4908307 := by
    simpa [prefixWord, tailWord_4908307, baseEnd_4908307] using wordTrace_append hprefix tailTrace_4908307
  have hstable : (prefixWord ++ tailWord_4908307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908307).length < 2 ^ (prefixWord ++ tailWord_4908307).sum := by decide
  have hdescent : baseEnd_4908307 < baseStart_4908307 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908324 : List Nat := [2, 3, 1, 3, 1, 1, 2, 2, 4, 2, 2]
def baseStart_4908324 : Nat := 118140960795 + 4908324 * 2 ^ 59
def prefixEnd_4908324 : Nat := 4983230072969 + 3 ^ 40 * 4908324 * 2
def baseEnd_4908324 : Nat := 2520329419998959393477035

theorem tailTrace_4908324 : CollatzResearch.WordTrace tailWord_4908324 prefixEnd_4908324 2520329419998959393477035 := by
  unfold tailWord_4908324
  simp only [CollatzResearch.WordTrace]
  refine ⟨89510641734993948922914013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119347522313325265230552017 89510641734993948922914013)
  ·
    refine ⟨33566490650622730846092755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89510641734993948922914013 33566490650622730846092755)
    ·
      refine ⟨50349735975934096269139133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33566490650622730846092755 50349735975934096269139133)
      ·
        refine ⟨18881150990975286100927175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50349735975934096269139133 18881150990975286100927175)
        ·
          refine ⟨28321726486462929151390763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18881150990975286100927175 28321726486462929151390763)
          ·
            refine ⟨42482589729694393727086145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28321726486462929151390763 42482589729694393727086145)
            ·
              refine ⟨31861942297270795295314609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42482589729694393727086145 31861942297270795295314609)
              ·
                refine ⟨23896456722953096471485957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31861942297270795295314609 23896456722953096471485957)
                ·
                  refine ⟨4480585635553705588403617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23896456722953096471485957 4480585635553705588403617)
                  ·
                    refine ⟨3360439226665279191302713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480585635553705588403617 3360439226665279191302713)
                    ·
                      refine ⟨2520329419998959393477035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360439226665279191302713 2520329419998959393477035)
                      ·
                        rfl

theorem cell23_4908324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 2, 4, 2, 2].length) (baseStart_4908324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908324 prefixEnd_4908324 := by exact prefixLift 4908324
  have htrace : WordTrace (prefixWord ++ tailWord_4908324) baseStart_4908324 baseEnd_4908324 := by
    simpa [prefixWord, tailWord_4908324, baseEnd_4908324] using wordTrace_append hprefix tailTrace_4908324
  have hstable : (prefixWord ++ tailWord_4908324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908324).length < 2 ^ (prefixWord ++ tailWord_4908324).sum := by decide
  have hdescent : baseEnd_4908324 < baseStart_4908324 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908328 : List Nat := [2, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2]
def baseStart_4908328 : Nat := 118140960795 + 4908328 * 2 ^ 59
def prefixEnd_4908328 : Nat := 4983230072969 + 3 ^ 40 * 4908328 * 2
def baseEnd_4908328 : Nat := 2520331473921577377827017

theorem tailTrace_4908328 : CollatzResearch.WordTrace tailWord_4908328 prefixEnd_4908328 2520331473921577377827017 := by
  unfold tailWord_4908328
  simp only [CollatzResearch.WordTrace]
  refine ⟨89510714680986703264486819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119347619574648937685982425 89510714680986703264486819)
  ·
    refine ⟨134266072021480054896730229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89510714680986703264486819 134266072021480054896730229)
    ·
      refine ⟨12587444252013755146568459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134266072021480054896730229 12587444252013755146568459)
      ·
        refine ⟨18881166378020632719852689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12587444252013755146568459 18881166378020632719852689)
        ·
          refine ⟨14160874783515474539889517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18881166378020632719852689 14160874783515474539889517)
          ·
            refine ⟨5310328043818302952458569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14160874783515474539889517 5310328043818302952458569)
            ·
              refine ⟨3982746032863727214343927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5310328043818302952458569 3982746032863727214343927)
              ·
                refine ⟨5974119049295590821515891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982746032863727214343927 5974119049295590821515891)
                ·
                  refine ⟨8961178573943386232273837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974119049295590821515891 8961178573943386232273837)
                  ·
                    refine ⟨3360441965228769837102689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8961178573943386232273837 3360441965228769837102689)
                    ·
                      refine ⟨2520331473921577377827017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360441965228769837102689 2520331473921577377827017)
                      ·
                        rfl

theorem cell23_4908328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 3, 2, 1, 1, 3, 2].length) (baseStart_4908328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908328 prefixEnd_4908328 := by exact prefixLift 4908328
  have htrace : WordTrace (prefixWord ++ tailWord_4908328) baseStart_4908328 baseEnd_4908328 := by
    simpa [prefixWord, tailWord_4908328, baseEnd_4908328] using wordTrace_append hprefix tailTrace_4908328
  have hstable : (prefixWord ++ tailWord_4908328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908328).length < 2 ^ (prefixWord ++ tailWord_4908328).sum := by decide
  have hdescent : baseEnd_4908328 < baseStart_4908328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908341 : List Nat := [1, 3, 3, 1, 2, 2, 3, 2, 2, 2, 2]
def baseStart_4908341 : Nat := 118140960795 + 4908341 * 2 ^ 59
def prefixEnd_4908341 : Nat := 4983230072969 + 3 ^ 40 * 4908341 * 2
def baseEnd_4908341 : Nat := 2520338149170085826964457

theorem tailTrace_4908341 : CollatzResearch.WordTrace tailWord_4908341 prefixEnd_4908341 2520338149170085826964457 := by
  unfold tailWord_4908341
  simp only [CollatzResearch.WordTrace]
  refine ⟨179021903510926309749196877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119347935673950873166131251 179021903510926309749196877)
  ·
    refine ⟨67133213816597366155948829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179021903510926309749196877 67133213816597366155948829)
    ·
      refine ⟨25174955181224012308480811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67133213816597366155948829 25174955181224012308480811)
      ·
        refine ⟨37762432771836018462721217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25174955181224012308480811 37762432771836018462721217)
        ·
          refine ⟨28321824578877013847040913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37762432771836018462721217 28321824578877013847040913)
          ·
            refine ⟨21241368434157760385280685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28321824578877013847040913 21241368434157760385280685)
            ·
              refine ⟨7965513162809160144480257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21241368434157760385280685 7965513162809160144480257)
              ·
                refine ⟨5974134872106870108360193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7965513162809160144480257 5974134872106870108360193)
                ·
                  refine ⟨4480601154080152581270145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974134872106870108360193 4480601154080152581270145)
                  ·
                    refine ⟨3360450865560114435952609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4480601154080152581270145 3360450865560114435952609)
                    ·
                      refine ⟨2520338149170085826964457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360450865560114435952609 2520338149170085826964457)
                      ·
                        rfl

theorem cell23_4908341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 3, 2, 2, 2, 2].length) (baseStart_4908341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908341 prefixEnd_4908341 := by exact prefixLift 4908341
  have htrace : WordTrace (prefixWord ++ tailWord_4908341) baseStart_4908341 baseEnd_4908341 := by
    simpa [prefixWord, tailWord_4908341, baseEnd_4908341] using wordTrace_append hprefix tailTrace_4908341
  have hstable : (prefixWord ++ tailWord_4908341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908341).length < 2 ^ (prefixWord ++ tailWord_4908341).sum := by decide
  have hdescent : baseEnd_4908341 < baseStart_4908341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908370 : List Nat := [3, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_4908370 : Nat := 118140960795 + 4908370 * 2 ^ 59
def prefixEnd_4908370 : Nat := 4983230072969 + 3 ^ 40 * 4908370 * 2
def baseEnd_4908370 : Nat := 2520353040109066213501823

theorem tailTrace_4908370 : CollatzResearch.WordTrace tailWord_4908370 prefixEnd_4908370 2520353040109066213501823 := by
  unfold tailWord_4908370
  simp only [CollatzResearch.WordTrace]
  refine ⟨44755740306955311925500641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119348640818547498468001709 44755740306955311925500641)
  ·
    refine ⟨33566805230216483944125481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44755740306955311925500641 33566805230216483944125481)
    ·
      refine ⟨25175103922662362958094111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33566805230216483944125481 25175103922662362958094111)
      ·
        refine ⟨37762655883993544437141167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175103922662362958094111 37762655883993544437141167)
        ·
          refine ⟨56643983825990316655711751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37762655883993544437141167 56643983825990316655711751)
          ·
            refine ⟨84965975738985474983567627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56643983825990316655711751 84965975738985474983567627)
            ·
              refine ⟨127448963608478212475351441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84965975738985474983567627 127448963608478212475351441)
              ·
                refine ⟨95586722706358659356513581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127448963608478212475351441 95586722706358659356513581)
                ·
                  refine ⟨35845021014884497258692593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 95586722706358659356513581 35845021014884497258692593)
                  ·
                    refine ⟨26883765761163372944019445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35845021014884497258692593 26883765761163372944019445)
                    ·
                      refine ⟨2520353040109066213501823, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26883765761163372944019445 2520353040109066213501823)
                      ·
                        rfl

theorem cell23_4908370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_4908370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908370 prefixEnd_4908370 := by exact prefixLift 4908370
  have htrace : WordTrace (prefixWord ++ tailWord_4908370) baseStart_4908370 baseEnd_4908370 := by
    simpa [prefixWord, tailWord_4908370, baseEnd_4908370] using wordTrace_append hprefix tailTrace_4908370
  have hstable : (prefixWord ++ tailWord_4908370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908370).length < 2 ^ (prefixWord ++ tailWord_4908370).sum := by decide
  have hdescent : baseEnd_4908370 < baseStart_4908370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908394 : List Nat := [3, 1, 3, 3, 2, 1, 1, 2, 2, 5]
def baseStart_4908394 : Nat := 118140960795 + 4908394 * 2 ^ 59
def prefixEnd_4908394 : Nat := 4983230072969 + 3 ^ 40 * 4908394 * 2
def baseEnd_4908394 : Nat := 840121787881591373200571

theorem tailTrace_4908394 : CollatzResearch.WordTrace tailWord_4908394 prefixEnd_4908394 840121787881591373200571 := by
  unfold tailWord_4908394
  simp only [CollatzResearch.WordTrace]
  refine ⟨44755959144933574950219059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119349224386489533200584157 44755959144933574950219059)
  ·
    refine ⟨67133938717400362425328589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44755959144933574950219059 67133938717400362425328589)
    ·
      refine ⟨25175227019025135909498221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67133938717400362425328589 25175227019025135909498221)
      ·
        refine ⟨9440710132134425966061833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25175227019025135909498221 9440710132134425966061833)
        ·
          refine ⟨7080532599100819474546375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9440710132134425966061833 7080532599100819474546375)
          ·
            refine ⟨10620798898651229211819563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080532599100819474546375 10620798898651229211819563)
            ·
              refine ⟨15931198347976843817729345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10620798898651229211819563 15931198347976843817729345)
              ·
                refine ⟨11948398760982632863297009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15931198347976843817729345 11948398760982632863297009)
                ·
                  refine ⟨8961299070736974647472757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11948398760982632863297009 8961299070736974647472757)
                  ·
                    refine ⟨840121787881591373200571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8961299070736974647472757 840121787881591373200571)
                    ·
                      rfl

theorem cell23_4908394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 1, 1, 2, 2, 5].length) (baseStart_4908394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908394 prefixEnd_4908394 := by exact prefixLift 4908394
  have htrace : WordTrace (prefixWord ++ tailWord_4908394) baseStart_4908394 baseEnd_4908394 := by
    simpa [prefixWord, tailWord_4908394, baseEnd_4908394] using wordTrace_append hprefix tailTrace_4908394
  have hstable : (prefixWord ++ tailWord_4908394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908394).length < 2 ^ (prefixWord ++ tailWord_4908394).sum := by decide
  have hdescent : baseEnd_4908394 < baseStart_4908394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908397 : List Nat := [1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_4908397 : Nat := 118140960795 + 4908397 * 2 ^ 59
def prefixEnd_4908397 : Nat := 4983230072969 + 3 ^ 40 * 4908397 * 2
def baseEnd_4908397 : Nat := 2520366904086737607864199

theorem tailTrace_4908397 : CollatzResearch.WordTrace tailWord_4908397 prefixEnd_4908397 2520366904086737607864199 := by
  unfold tailWord_4908397
  simp only [CollatzResearch.WordTrace]
  refine ⟨179023945998723431313235445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119349297332482287542156963 179023945998723431313235445)
  ·
    refine ⟨16783494937380321685615823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179023945998723431313235445 16783494937380321685615823)
    ·
      refine ⟨25175242406070482528423735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16783494937380321685615823 25175242406070482528423735)
      ·
        refine ⟨37762863609105723792635603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175242406070482528423735 37762863609105723792635603)
        ·
          refine ⟨56644295413658585688953405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37762863609105723792635603 56644295413658585688953405)
          ·
            refine ⟨21241610780121969633357527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56644295413658585688953405 21241610780121969633357527)
            ·
              refine ⟨31862416170182954450036291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21241610780121969633357527 31862416170182954450036291)
              ·
                refine ⟨47793624255274431675054437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31862416170182954450036291 47793624255274431675054437)
                ·
                  refine ⟨8961304547863955939072707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47793624255274431675054437 8961304547863955939072707)
                  ·
                    refine ⟨13441956821795933908609061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8961304547863955939072707 13441956821795933908609061)
                    ·
                      refine ⟨2520366904086737607864199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13441956821795933908609061 2520366904086737607864199)
                      ·
                        rfl

theorem cell23_4908397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_4908397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908397 prefixEnd_4908397 := by exact prefixLift 4908397
  have htrace : WordTrace (prefixWord ++ tailWord_4908397) baseStart_4908397 baseEnd_4908397 := by
    simpa [prefixWord, tailWord_4908397, baseEnd_4908397] using wordTrace_append hprefix tailTrace_4908397
  have hstable : (prefixWord ++ tailWord_4908397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908397).length < 2 ^ (prefixWord ++ tailWord_4908397).sum := by decide
  have hdescent : baseEnd_4908397 < baseStart_4908397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908398 : List Nat := [4, 1, 2, 4, 1, 1, 3, 2, 5]
def baseStart_4908398 : Nat := 118140960795 + 4908398 * 2 ^ 59
def prefixEnd_4908398 : Nat := 4983230072969 + 3 ^ 40 * 4908398 * 2
def baseEnd_4908398 : Nat := 280040824174154678216855

theorem tailTrace_4908398 : CollatzResearch.WordTrace tailWord_4908398 prefixEnd_4908398 280040824174154678216855 := by
  unfold tailWord_4908398
  simp only [CollatzResearch.WordTrace]
  refine ⟨22377997808964976060502731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119349321647813205656014565 22377997808964976060502731)
  ·
    refine ⟨33566996713447464090754097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22377997808964976060502731 33566996713447464090754097)
    ·
      refine ⟨25175247535085598068065573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33566996713447464090754097 25175247535085598068065573)
      ·
        refine ⟨4720358912828549637762295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25175247535085598068065573 4720358912828549637762295)
        ·
          refine ⟨7080538369242824456643443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720358912828549637762295 7080538369242824456643443)
          ·
            refine ⟨10620807553864236684965165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080538369242824456643443 10620807553864236684965165)
            ·
              refine ⟨3982802832699088756861937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10620807553864236684965165 3982802832699088756861937)
              ·
                refine ⟨2987102124524316567646453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3982802832699088756861937 2987102124524316567646453)
                ·
                  refine ⟨280040824174154678216855, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987102124524316567646453 280040824174154678216855)
                  ·
                    rfl

theorem cell23_4908398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_4908398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908398 prefixEnd_4908398 := by exact prefixLift 4908398
  have htrace : WordTrace (prefixWord ++ tailWord_4908398) baseStart_4908398 baseEnd_4908398 := by
    simpa [prefixWord, tailWord_4908398, baseEnd_4908398] using wordTrace_append hprefix tailTrace_4908398
  have hstable : (prefixWord ++ tailWord_4908398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908398).length < 2 ^ (prefixWord ++ tailWord_4908398).sum := by decide
  have hdescent : baseEnd_4908398 < baseStart_4908398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908457 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 5, 5, 2]
def baseStart_4908457 : Nat := 118140960795 + 4908457 * 2 ^ 59
def prefixEnd_4908457 : Nat := 4983230072969 + 3 ^ 40 * 4908457 * 2
def baseEnd_4908457 : Nat := 2520397712926007373113923

theorem tailTrace_4908457 : CollatzResearch.WordTrace tailWord_4908457 prefixEnd_4908457 2520397712926007373113923 := by
  unfold tailWord_4908457
  simp only [CollatzResearch.WordTrace]
  refine ⟨179026134378506061560419625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119350756252337374373613083 179026134378506061560419625)
  ·
    refine ⟨134269600783879546170314719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179026134378506061560419625 134269600783879546170314719)
    ·
      refine ⟨201404401175819319255472079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134269600783879546170314719 201404401175819319255472079)
      ·
        refine ⟨302106601763728978883208119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201404401175819319255472079 302106601763728978883208119)
        ·
          refine ⟨453159902645593468324812179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302106601763728978883208119 453159902645593468324812179)
          ·
            refine ⟨679739853968390202487218269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 453159902645593468324812179 679739853968390202487218269)
            ·
              refine ⟨254902445238146325932706851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 679739853968390202487218269 254902445238146325932706851)
              ·
                refine ⟨382353667857219488899060277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 254902445238146325932706851 382353667857219488899060277)
                ·
                  refine ⟨35845656361614327084286901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 382353667857219488899060277 35845656361614327084286901)
                  ·
                    refine ⟨3360530283901343164151897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 35845656361614327084286901 3360530283901343164151897)
                    ·
                      refine ⟨2520397712926007373113923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360530283901343164151897 2520397712926007373113923)
                      ·
                        rfl

theorem cell23_4908457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 5, 5, 2].length) (baseStart_4908457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908457 prefixEnd_4908457 := by exact prefixLift 4908457
  have htrace : WordTrace (prefixWord ++ tailWord_4908457) baseStart_4908457 baseEnd_4908457 := by
    simpa [prefixWord, tailWord_4908457, baseEnd_4908457] using wordTrace_append hprefix tailTrace_4908457
  have hstable : (prefixWord ++ tailWord_4908457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908457).length < 2 ^ (prefixWord ++ tailWord_4908457).sum := by decide
  have hdescent : baseEnd_4908457 < baseStart_4908457 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908482 : List Nat := [3, 5, 2, 1, 1, 2, 1, 1, 2, 1, 4]
def baseStart_4908482 : Nat := 118140960795 + 4908482 * 2 ^ 59
def prefixEnd_4908482 : Nat := 4983230072969 + 3 ^ 40 * 4908482 * 2
def baseEnd_4908482 : Nat := 2520410549942369775301309

theorem tailTrace_4908482 : CollatzResearch.WordTrace tailWord_4908482 prefixEnd_4908482 2520410549942369775301309 := by
  unfold tailWord_4908482
  simp only [CollatzResearch.WordTrace]
  refine ⟨44756761550853872707519925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119351364135610327220053133 44756761550853872707519925)
  ·
    refine ⟨4195946395392550566329993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 44756761550853872707519925 4195946395392550566329993)
    ·
      refine ⟨3146959796544412924747495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4195946395392550566329993 3146959796544412924747495)
      ·
        refine ⟨4720439694816619387121243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3146959796544412924747495 4720439694816619387121243)
        ·
          refine ⟨7080659542224929080681865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4720439694816619387121243 7080659542224929080681865)
          ·
            refine ⟨5310494656668696810511399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7080659542224929080681865 5310494656668696810511399)
            ·
              refine ⟨7965741985003045215767099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310494656668696810511399 7965741985003045215767099)
              ·
                refine ⟨11948612977504567823650649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7965741985003045215767099 11948612977504567823650649)
                ·
                  refine ⟨8961459733128425867737987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11948612977504567823650649 8961459733128425867737987)
                  ·
                    refine ⟨13442189599692638801606981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8961459733128425867737987 13442189599692638801606981)
                    ·
                      refine ⟨2520410549942369775301309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13442189599692638801606981 2520410549942369775301309)
                      ·
                        rfl

theorem cell23_4908482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_4908482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908482 prefixEnd_4908482 := by exact prefixLift 4908482
  have htrace : WordTrace (prefixWord ++ tailWord_4908482) baseStart_4908482 baseEnd_4908482 := by
    simpa [prefixWord, tailWord_4908482, baseEnd_4908482] using wordTrace_append hprefix tailTrace_4908482
  have hstable : (prefixWord ++ tailWord_4908482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908482).length < 2 ^ (prefixWord ++ tailWord_4908482).sum := by decide
  have hdescent : baseEnd_4908482 < baseStart_4908482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908484 : List Nat := [2, 3, 3, 2, 1, 1, 2, 1, 3, 5]
def baseStart_4908484 : Nat := 118140960795 + 4908484 * 2 ^ 59
def prefixEnd_4908484 : Nat := 4983230072969 + 3 ^ 40 * 4908484 * 2
def baseEnd_4908484 : Nat := 840137192301226255825433

theorem tailTrace_4908484 : CollatzResearch.WordTrace tailWord_4908484 prefixEnd_4908484 840137192301226255825433 := by
  unfold tailWord_4908484
  simp only [CollatzResearch.WordTrace]
  refine ⟨89513559574704122585826253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119351412766272163447768337 89513559574704122585826253)
  ·
    refine ⟨33567584840514045969684845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89513559574704122585826253 33567584840514045969684845)
    ·
      refine ⟨12587844315192767238631817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 33567584840514045969684845 12587844315192767238631817)
      ·
        refine ⟨9440883236394575428973863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12587844315192767238631817 9440883236394575428973863)
        ·
          refine ⟨14161324854591863143460795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9440883236394575428973863 14161324854591863143460795)
          ·
            refine ⟨21241987281887794715191193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14161324854591863143460795 21241987281887794715191193)
            ·
              refine ⟨15931490461415846036393395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21241987281887794715191193 15931490461415846036393395)
              ·
                refine ⟨23897235692123769054590093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15931490461415846036393395 23897235692123769054590093)
                ·
                  refine ⟨8961463384546413395471285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23897235692123769054590093 8961463384546413395471285)
                  ·
                    refine ⟨840137192301226255825433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8961463384546413395471285 840137192301226255825433)
                    ·
                      rfl

theorem cell23_4908484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 1, 3, 5].length) (baseStart_4908484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908484 prefixEnd_4908484 := by exact prefixLift 4908484
  have htrace : WordTrace (prefixWord ++ tailWord_4908484) baseStart_4908484 baseEnd_4908484 := by
    simpa [prefixWord, tailWord_4908484, baseEnd_4908484] using wordTrace_append hprefix tailTrace_4908484
  have hstable : (prefixWord ++ tailWord_4908484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908484).length < 2 ^ (prefixWord ++ tailWord_4908484).sum := by decide
  have hdescent : baseEnd_4908484 < baseStart_4908484 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908487 : List Nat := [1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4]
def baseStart_4908487 : Nat := 118140960795 + 4908487 * 2 ^ 59
def prefixEnd_4908487 : Nat := 4983230072969 + 3 ^ 40 * 4908487 * 2
def baseEnd_4908487 : Nat := 2520413117345642255738785

theorem tailTrace_4908487 : CollatzResearch.WordTrace tailWord_4908487 prefixEnd_4908487 2520413117345642255738785 := by
  unfold tailWord_4908487
  simp only [CollatzResearch.WordTrace]
  refine ⟨179027228568397376684011715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119351485712264917789341143 179027228568397376684011715)
  ·
    refine ⟨268540842852596065026017573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179027228568397376684011715 268540842852596065026017573)
    ·
      refine ⟨50351408034861762192378295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268540842852596065026017573 50351408034861762192378295)
      ·
        refine ⟨75527112052292643288567443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50351408034861762192378295 75527112052292643288567443)
        ·
          refine ⟨113290668078438964932851165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75527112052292643288567443 113290668078438964932851165)
          ·
            refine ⟨42484000529414611849819187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113290668078438964932851165 42484000529414611849819187)
            ·
              refine ⟨63726000794121917774728781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42484000529414611849819187 63726000794121917774728781)
              ·
                refine ⟨23897250297795719165523293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63726000794121917774728781 23897250297795719165523293)
                ·
                  refine ⟨8961468861673394687071235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23897250297795719165523293 8961468861673394687071235)
                  ·
                    refine ⟨13442203292510092030606853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8961468861673394687071235 13442203292510092030606853)
                    ·
                      refine ⟨2520413117345642255738785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13442203292510092030606853 2520413117345642255738785)
                      ·
                        rfl

theorem cell23_4908487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 3, 3, 1, 4].length) (baseStart_4908487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908487 prefixEnd_4908487 := by exact prefixLift 4908487
  have htrace : WordTrace (prefixWord ++ tailWord_4908487) baseStart_4908487 baseEnd_4908487 := by
    simpa [prefixWord, tailWord_4908487, baseEnd_4908487] using wordTrace_append hprefix tailTrace_4908487
  have hstable : (prefixWord ++ tailWord_4908487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908487).length < 2 ^ (prefixWord ++ tailWord_4908487).sum := by decide
  have hdescent : baseEnd_4908487 < baseStart_4908487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908534 : List Nat := [5, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6]
def baseStart_4908534 : Nat := 118140960795 + 4908534 * 2 ^ 59
def prefixEnd_4908534 : Nat := 4983230072969 + 3 ^ 40 * 4908534 * 2
def baseEnd_4908534 : Nat := 2520437250936403571851069

theorem tailTrace_4908534 : CollatzResearch.WordTrace tailWord_4908534 prefixEnd_4908534 2520437250936403571851069 := by
  unfold tailWord_4908534
  simp only [CollatzResearch.WordTrace]
  refine ⟨11189308924951693981935791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119352628532818069140648437 11189308924951693981935791)
  ·
    refine ⟨16783963387427540972903687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11189308924951693981935791 16783963387427540972903687)
    ·
      refine ⟨25175945081141311459355531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16783963387427540972903687 25175945081141311459355531)
      ·
        refine ⟨37763917621711967189033297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25175945081141311459355531 37763917621711967189033297)
        ·
          refine ⟨28322938216283975391774973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37763917621711967189033297 28322938216283975391774973)
          ·
            refine ⟨10621101831106490771915615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28322938216283975391774973 10621101831106490771915615)
            ·
              refine ⟨15931652746659736157873423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10621101831106490771915615 15931652746659736157873423)
              ·
                refine ⟨23897479119989604236810135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15931652746659736157873423 23897479119989604236810135)
                ·
                  refine ⟨35846218679984406355215203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23897479119989604236810135 35846218679984406355215203)
                  ·
                    refine ⟨53769328019976609532822805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35846218679984406355215203 53769328019976609532822805)
                    ·
                      refine ⟨2520437250936403571851069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53769328019976609532822805 2520437250936403571851069)
                      ·
                        rfl

theorem cell23_4908534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 3, 1, 1, 1, 1, 6].length) (baseStart_4908534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908534 prefixEnd_4908534 := by exact prefixLift 4908534
  have htrace : WordTrace (prefixWord ++ tailWord_4908534) baseStart_4908534 baseEnd_4908534 := by
    simpa [prefixWord, tailWord_4908534, baseEnd_4908534] using wordTrace_append hprefix tailTrace_4908534
  have hstable : (prefixWord ++ tailWord_4908534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908534).length < 2 ^ (prefixWord ++ tailWord_4908534).sum := by decide
  have hdescent : baseEnd_4908534 < baseStart_4908534 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908541 : List Nat := [1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 3]
def baseStart_4908541 : Nat := 118140960795 + 4908541 * 2 ^ 59
def prefixEnd_4908541 : Nat := 4983230072969 + 3 ^ 40 * 4908541 * 2
def baseEnd_4908541 : Nat := 2520440845300985044463537

theorem tailTrace_4908541 : CollatzResearch.WordTrace tailWord_4908541 prefixEnd_4908541 2520440845300985044463537 := by
  unfold tailWord_4908541
  simp only [CollatzResearch.WordTrace]
  refine ⟨179029198110201743906477477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119352798740134495937651651 179029198110201743906477477)
  ·
    refine ⟨33567974645662826982464527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 179029198110201743906477477 33567974645662826982464527)
    ·
      refine ⟨50351961968494240473696791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33567974645662826982464527 50351961968494240473696791)
      ·
        refine ⟨75527942952741360710545187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50351961968494240473696791 75527942952741360710545187)
        ·
          refine ⟨113291914429112041065817781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75527942952741360710545187 113291914429112041065817781)
          ·
            refine ⟨10621116977729253849920417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113291914429112041065817781 10621116977729253849920417)
            ·
              refine ⟨7965837733296940387440313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10621116977729253849920417 7965837733296940387440313)
              ·
                refine ⟨5974378299972705290580235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7965837733296940387440313 5974378299972705290580235)
                ·
                  refine ⟨8961567449959057935870353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974378299972705290580235 8961567449959057935870353)
                  ·
                    refine ⟨6721175587469293451902765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8961567449959057935870353 6721175587469293451902765)
                    ·
                      refine ⟨2520440845300985044463537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721175587469293451902765 2520440845300985044463537)
                      ·
                        rfl

theorem cell23_4908541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 2, 1, 2, 3].length) (baseStart_4908541 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908541 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908541 prefixEnd_4908541 := by exact prefixLift 4908541
  have htrace : WordTrace (prefixWord ++ tailWord_4908541) baseStart_4908541 baseEnd_4908541 := by
    simpa [prefixWord, tailWord_4908541, baseEnd_4908541] using wordTrace_append hprefix tailTrace_4908541
  have hstable : (prefixWord ++ tailWord_4908541).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908541).length < 2 ^ (prefixWord ++ tailWord_4908541).sum := by decide
  have hdescent : baseEnd_4908541 < baseStart_4908541 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908615 : List Nat := [1, 1, 4, 1, 5, 1, 3, 1, 1, 3, 2]
def baseStart_4908615 : Nat := 118140960795 + 4908615 * 2 ^ 59
def prefixEnd_4908615 : Nat := 4983230072969 + 3 ^ 40 * 4908615 * 2
def baseEnd_4908615 : Nat := 2520478842869417754938197

theorem tailTrace_4908615 : CollatzResearch.WordTrace tailWord_4908615 prefixEnd_4908615 2520478842869417754938197 := by
  unfold tailWord_4908615
  simp only [CollatzResearch.WordTrace]
  refine ⟨179031897111933654544671299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119354598074622436363114199 179031897111933654544671299)
  ·
    refine ⟨268547845667900481817006949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179031897111933654544671299 268547845667900481817006949)
    ·
      refine ⟨50352721062731340340688803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268547845667900481817006949 50352721062731340340688803)
      ·
        refine ⟨75529081594097010511033205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50352721062731340340688803 75529081594097010511033205)
        ·
          refine ⟨7080851399446594735409363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75529081594097010511033205 7080851399446594735409363)
          ·
            refine ⟨10621277099169892103114045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7080851399446594735409363 10621277099169892103114045)
            ·
              refine ⟨3982978912188709538667767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10621277099169892103114045 3982978912188709538667767)
              ·
                refine ⟨5974468368283064308001651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3982978912188709538667767 5974468368283064308001651)
                ·
                  refine ⟨8961702552424596462002477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974468368283064308001651 8961702552424596462002477)
                  ·
                    refine ⟨3360638457159223673250929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8961702552424596462002477 3360638457159223673250929)
                    ·
                      refine ⟨2520478842869417754938197, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360638457159223673250929 2520478842869417754938197)
                      ·
                        rfl

theorem cell23_4908615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 3, 1, 1, 3, 2].length) (baseStart_4908615 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908615 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908615 prefixEnd_4908615 := by exact prefixLift 4908615
  have htrace : WordTrace (prefixWord ++ tailWord_4908615) baseStart_4908615 baseEnd_4908615 := by
    simpa [prefixWord, tailWord_4908615, baseEnd_4908615] using wordTrace_append hprefix tailTrace_4908615
  have hstable : (prefixWord ++ tailWord_4908615).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908615).length < 2 ^ (prefixWord ++ tailWord_4908615).sum := by decide
  have hdescent : baseEnd_4908615 < baseStart_4908615 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908644 : List Nat := [2, 3, 1, 1, 2, 3, 1, 1, 1, 5, 3]
def baseStart_4908644 : Nat := 118140960795 + 4908644 * 2 ^ 59
def prefixEnd_4908644 : Nat := 4983230072969 + 3 ^ 40 * 4908644 * 2
def baseEnd_4908644 : Nat := 2520493733808398141475563

theorem tailTrace_4908644 : CollatzResearch.WordTrace tailWord_4908644 prefixEnd_4908644 2520493733808398141475563 := by
  unfold tailWord_4908644
  simp only [CollatzResearch.WordTrace]
  refine ⟨89516477414414296248738493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119355303219219061664984657 89516477414414296248738493)
  ·
    refine ⟨33568679030405361093276935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89516477414414296248738493 33568679030405361093276935)
    ·
      refine ⟨50353018545608041639915403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33568679030405361093276935 50353018545608041639915403)
      ·
        refine ⟨75529527818412062459873105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50353018545608041639915403 75529527818412062459873105)
        ·
          refine ⟨56647145863809046844904829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75529527818412062459873105 56647145863809046844904829)
          ·
            refine ⟨21242679698928392566839311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56647145863809046844904829 21242679698928392566839311)
            ·
              refine ⟨31864019548392588850258967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21242679698928392566839311 31864019548392588850258967)
              ·
                refine ⟨47796029322588883275388451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31864019548392588850258967 47796029322588883275388451)
                ·
                  refine ⟨71694043983883324913082677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47796029322588883275388451 71694043983883324913082677)
                  ·
                    refine ⟨6721316623489061710601501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71694043983883324913082677 6721316623489061710601501)
                    ·
                      refine ⟨2520493733808398141475563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721316623489061710601501 2520493733808398141475563)
                      ·
                        rfl

theorem cell23_4908644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 1, 1, 5, 3].length) (baseStart_4908644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908644 prefixEnd_4908644 := by exact prefixLift 4908644
  have htrace : WordTrace (prefixWord ++ tailWord_4908644) baseStart_4908644 baseEnd_4908644 := by
    simpa [prefixWord, tailWord_4908644, baseEnd_4908644] using wordTrace_append hprefix tailTrace_4908644
  have hstable : (prefixWord ++ tailWord_4908644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908644).length < 2 ^ (prefixWord ++ tailWord_4908644).sum := by decide
  have hdescent : baseEnd_4908644 < baseStart_4908644 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908657 : List Nat := [1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 7]
def baseStart_4908657 : Nat := 118140960795 + 4908657 * 2 ^ 59
def prefixEnd_4908657 : Nat := 4983230072969 + 3 ^ 40 * 4908657 * 2
def baseEnd_4908657 : Nat := 2520500409056906590613003

theorem tailTrace_4908657 : CollatzResearch.WordTrace tailWord_4908657 prefixEnd_4908657 2520500409056906590613003 := by
  unfold tailWord_4908657
  simp only [CollatzResearch.WordTrace]
  refine ⟨179033428977781495717700225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119355619318520997145133483 179033428977781495717700225)
  ·
    refine ⟨134275071733336121788275169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179033428977781495717700225 134275071733336121788275169)
    ·
      refine ⟨100706303800002091341206377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134275071733336121788275169 100706303800002091341206377)
      ·
        refine ⟨75529727850001568505904783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100706303800002091341206377 75529727850001568505904783)
        ·
          refine ⟨113294591775002352758857175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75529727850001568505904783 113294591775002352758857175)
          ·
            refine ⟨169941887662503529138285763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113294591775002352758857175 169941887662503529138285763)
            ·
              refine ⟨254912831493755293707428645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169941887662503529138285763 254912831493755293707428645)
              ·
                refine ⟨47796155905079117570142871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 254912831493755293707428645 47796155905079117570142871)
                ·
                  refine ⟨71694233857618676355214307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47796155905079117570142871 71694233857618676355214307)
                  ·
                    refine ⟨107541350786428014532821461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71694233857618676355214307 107541350786428014532821461)
                    ·
                      refine ⟨2520500409056906590613003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107541350786428014532821461 2520500409056906590613003)
                      ·
                        rfl

theorem cell23_4908657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_4908657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908657 prefixEnd_4908657 := by exact prefixLift 4908657
  have htrace : WordTrace (prefixWord ++ tailWord_4908657) baseStart_4908657 baseEnd_4908657 := by
    simpa [prefixWord, tailWord_4908657, baseEnd_4908657] using wordTrace_append hprefix tailTrace_4908657
  have hstable : (prefixWord ++ tailWord_4908657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908657).length < 2 ^ (prefixWord ++ tailWord_4908657).sum := by decide
  have hdescent : baseEnd_4908657 < baseStart_4908657 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908684 : List Nat := [2, 2, 1, 2, 1, 1, 4, 1, 4, 1, 4]
def baseStart_4908684 : Nat := 118140960795 + 4908684 * 2 ^ 59
def prefixEnd_4908684 : Nat := 4983230072969 + 3 ^ 40 * 4908684 * 2
def baseEnd_4908684 : Nat := 2520514273034577984975379

theorem tailTrace_4908684 : CollatzResearch.WordTrace tailWord_4908684 prefixEnd_4908684 2520514273034577984975379 := by
  unfold tailWord_4908684
  simp only [CollatzResearch.WordTrace]
  refine ⟨89517206874341839664466553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119356275832455786219288737 89517206874341839664466553)
  ·
    refine ⟨67137905155756379748349915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89517206874341839664466553 67137905155756379748349915)
    ·
      refine ⟨100706857733634569622524873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67137905155756379748349915 100706857733634569622524873)
      ·
        refine ⟨75530143300225927216893655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100706857733634569622524873 75530143300225927216893655)
        ·
          refine ⟨113295214950338890825340483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75530143300225927216893655 113295214950338890825340483)
          ·
            refine ⟨169942822425508336238010725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113295214950338890825340483 169942822425508336238010725)
            ·
              refine ⟨31864279204782813044627011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169942822425508336238010725 31864279204782813044627011)
              ·
                refine ⟨47796418807174219566940517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31864279204782813044627011 47796418807174219566940517)
                ·
                  refine ⟨8961828526345166168801347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47796418807174219566940517 8961828526345166168801347)
                  ·
                    refine ⟨13442742789517749253202021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8961828526345166168801347 13442742789517749253202021)
                    ·
                      refine ⟨2520514273034577984975379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13442742789517749253202021 2520514273034577984975379)
                      ·
                        rfl

theorem cell23_4908684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_4908684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908684 prefixEnd_4908684 := by exact prefixLift 4908684
  have htrace : WordTrace (prefixWord ++ tailWord_4908684) baseStart_4908684 baseEnd_4908684 := by
    simpa [prefixWord, tailWord_4908684, baseEnd_4908684] using wordTrace_append hprefix tailTrace_4908684
  have hstable : (prefixWord ++ tailWord_4908684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908684).length < 2 ^ (prefixWord ++ tailWord_4908684).sum := by decide
  have hdescent : baseEnd_4908684 < baseStart_4908684 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908778 : List Nat := [3, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2]
def baseStart_4908778 : Nat := 118140960795 + 4908778 * 2 ^ 59
def prefixEnd_4908778 : Nat := 4983230072969 + 3 ^ 40 * 4908778 * 2
def baseEnd_4908778 : Nat := 2520562540216100617199947

theorem tailTrace_4908778 : CollatzResearch.WordTrace tailWord_4908778 prefixEnd_4908778 2520562540216100617199947 := by
  unfold tailWord_4908778
  simp only [CollatzResearch.WordTrace]
  refine ⟨44759460552585783345713747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119358561473562088921903325 44759460552585783345713747)
  ·
    refine ⟨67139190828878675018570621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44759460552585783345713747 67139190828878675018570621)
    ·
      refine ⟨25177196560829503131963983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67139190828878675018570621 25177196560829503131963983)
      ·
        refine ⟨37765794841244254697945975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25177196560829503131963983 37765794841244254697945975)
        ·
          refine ⟨56648692261866382046918963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37765794841244254697945975 56648692261866382046918963)
          ·
            refine ⟨84973038392799573070378445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56648692261866382046918963 84973038392799573070378445)
            ·
              refine ⟨31864889397299839901391917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84973038392799573070378445 31864889397299839901391917)
              ·
                refine ⟨11949333523987439963021969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31864889397299839901391917 11949333523987439963021969)
                ·
                  refine ⟨8962000142990579972266477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11949333523987439963021969 8962000142990579972266477)
                  ·
                    refine ⟨3360750053621467489599929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8962000142990579972266477 3360750053621467489599929)
                    ·
                      refine ⟨2520562540216100617199947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360750053621467489599929 2520562540216100617199947)
                      ·
                        rfl

theorem cell23_4908778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 3, 3, 2, 3, 2].length) (baseStart_4908778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908778 prefixEnd_4908778 := by exact prefixLift 4908778
  have htrace : WordTrace (prefixWord ++ tailWord_4908778) baseStart_4908778 baseEnd_4908778 := by
    simpa [prefixWord, tailWord_4908778, baseEnd_4908778] using wordTrace_append hprefix tailTrace_4908778
  have hstable : (prefixWord ++ tailWord_4908778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908778).length < 2 ^ (prefixWord ++ tailWord_4908778).sum := by decide
  have hdescent : baseEnd_4908778 < baseStart_4908778 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908791 : List Nat := [1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 4]
def baseStart_4908791 : Nat := 118140960795 + 4908791 * 2 ^ 59
def prefixEnd_4908791 : Nat := 4983230072969 + 3 ^ 40 * 4908791 * 2
def baseEnd_4908791 : Nat := 2520569215464609066337387

theorem tailTrace_4908791 : CollatzResearch.WordTrace tailWord_4908791 prefixEnd_4908791 2520569215464609066337387 := by
  unfold tailWord_4908791
  simp only [CollatzResearch.WordTrace]
  refine ⟨179038316359296036603078227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119358877572864024402052151 179038316359296036603078227)
  ·
    refine ⟨268557474538944054904617341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179038316359296036603078227 268557474538944054904617341)
    ·
      refine ⟨100709052952104020589231503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268557474538944054904617341 100709052952104020589231503)
      ·
        refine ⟨151063579428156030883847255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100709052952104020589231503 151063579428156030883847255)
        ·
          refine ⟨226595369142234046325770883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151063579428156030883847255 226595369142234046325770883)
          ·
            refine ⟨339893053713351069488656325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226595369142234046325770883 339893053713351069488656325)
            ·
              refine ⟨63729947571253325529123061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 339893053713351069488656325 63729947571253325529123061)
              ·
                refine ⟨5974682584804999268355287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63729947571253325529123061 5974682584804999268355287)
                ·
                  refine ⟨8962023877207498902532931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974682584804999268355287 8962023877207498902532931)
                  ·
                    refine ⟨13443035815811248353799397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8962023877207498902532931 13443035815811248353799397)
                    ·
                      refine ⟨2520569215464609066337387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13443035815811248353799397 2520569215464609066337387)
                      ·
                        rfl

theorem cell23_4908791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 5, 1, 1, 4].length) (baseStart_4908791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908791 prefixEnd_4908791 := by exact prefixLift 4908791
  have htrace : WordTrace (prefixWord ++ tailWord_4908791) baseStart_4908791 baseEnd_4908791 := by
    simpa [prefixWord, tailWord_4908791, baseEnd_4908791] using wordTrace_append hprefix tailTrace_4908791
  have hstable : (prefixWord ++ tailWord_4908791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908791).length < 2 ^ (prefixWord ++ tailWord_4908791).sum := by decide
  have hdescent : baseEnd_4908791 < baseStart_4908791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908801 : List Nat := [1, 2, 4, 1, 1, 1, 2, 3, 4, 4]
def baseStart_4908801 : Nat := 118140960795 + 4908801 * 2 ^ 59
def prefixEnd_4908801 : Nat := 4983230072969 + 3 ^ 40 * 4908801 * 2
def baseEnd_4908801 : Nat := 840191450090384675737447

theorem tailTrace_4908801 : CollatzResearch.WordTrace tailWord_4908801 prefixEnd_4908801 840191450090384675737447 := by
  unfold tailWord_4908801
  simp only [CollatzResearch.WordTrace]
  refine ⟨179038681089259808310942257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119359120726173205540628171 179038681089259808310942257)
  ·
    refine ⟨134279010816944856233206693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179038681089259808310942257 134279010816944856233206693)
    ·
      refine ⟨25177314528177160543726255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 134279010816944856233206693 25177314528177160543726255)
      ·
        refine ⟨37765971792265740815589383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25177314528177160543726255 37765971792265740815589383)
        ·
          refine ⟨56648957688398611223384075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37765971792265740815589383 56648957688398611223384075)
          ·
            refine ⟨84973436532597916835076113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56648957688398611223384075 84973436532597916835076113)
            ·
              refine ⟨63730077399448437626307085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84973436532597916835076113 63730077399448437626307085)
              ·
                refine ⟨23898779024793164109865157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63730077399448437626307085 23898779024793164109865157)
                ·
                  refine ⟨4481021067148718270599717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23898779024793164109865157 4481021067148718270599717)
                  ·
                    refine ⟨840191450090384675737447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481021067148718270599717 840191450090384675737447)
                    ·
                      rfl

theorem cell23_4908801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 3, 4, 4].length) (baseStart_4908801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908801 prefixEnd_4908801 := by exact prefixLift 4908801
  have htrace : WordTrace (prefixWord ++ tailWord_4908801) baseStart_4908801 baseEnd_4908801 := by
    simpa [prefixWord, tailWord_4908801, baseEnd_4908801] using wordTrace_append hprefix tailTrace_4908801
  have hstable : (prefixWord ++ tailWord_4908801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908801).length < 2 ^ (prefixWord ++ tailWord_4908801).sum := by decide
  have hdescent : baseEnd_4908801 < baseStart_4908801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908802 : List Nat := [3, 4, 1, 1, 1, 1, 3, 4, 1, 1, 3]
def baseStart_4908802 : Nat := 118140960795 + 4908802 * 2 ^ 59
def prefixEnd_4908802 : Nat := 4983230072969 + 3 ^ 40 * 4908802 * 2
def baseEnd_4908802 : Nat := 2520574863751808523299837

theorem tailTrace_4908802 : CollatzResearch.WordTrace tailWord_4908802 prefixEnd_4908802 2520574863751808523299837 := by
  unfold tailWord_4908802
  simp only [CollatzResearch.WordTrace]
  refine ⟨44759679390564046370432165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119359145041504123654485773 44759679390564046370432165)
  ·
    refine ⟨8392439885730758694456031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44759679390564046370432165 8392439885730758694456031)
    ·
      refine ⟨12588659828596138041684047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8392439885730758694456031 12588659828596138041684047)
      ·
        refine ⟨18882989742894207062526071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12588659828596138041684047 18882989742894207062526071)
        ·
          refine ⟨28324484614341310593789107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18882989742894207062526071 28324484614341310593789107)
          ·
            refine ⟨42486726921511965890683661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28324484614341310593789107 42486726921511965890683661)
            ·
              refine ⟨15932522595566987209006373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42486726921511965890683661 15932522595566987209006373)
              ·
                refine ⟨2987347986668810101688695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15932522595566987209006373 2987347986668810101688695)
                ·
                  refine ⟨4481021980003215152533043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987347986668810101688695 4481021980003215152533043)
                  ·
                    refine ⟨6721532970004822728799565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4481021980003215152533043 6721532970004822728799565)
                    ·
                      refine ⟨2520574863751808523299837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721532970004822728799565 2520574863751808523299837)
                      ·
                        rfl

theorem cell23_4908802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 3, 4, 1, 1, 3].length) (baseStart_4908802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908802 prefixEnd_4908802 := by exact prefixLift 4908802
  have htrace : WordTrace (prefixWord ++ tailWord_4908802) baseStart_4908802 baseEnd_4908802 := by
    simpa [prefixWord, tailWord_4908802, baseEnd_4908802] using wordTrace_append hprefix tailTrace_4908802
  have hstable : (prefixWord ++ tailWord_4908802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908802).length < 2 ^ (prefixWord ++ tailWord_4908802).sum := by decide
  have hdescent : baseEnd_4908802 < baseStart_4908802 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908811 : List Nat := [1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3]
def baseStart_4908811 : Nat := 118140960795 + 4908811 * 2 ^ 59
def prefixEnd_4908811 : Nat := 4983230072969 + 3 ^ 40 * 4908811 * 2
def baseEnd_4908811 : Nat := 2520579485077698988087295

theorem tailTrace_4908811 : CollatzResearch.WordTrace tailWord_4908811 prefixEnd_4908811 2520579485077698988087295 := by
  unfold tailWord_4908811
  simp only [CollatzResearch.WordTrace]
  refine ⟨179039045819223580018806287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119359363879482386679204191 179039045819223580018806287)
  ·
    refine ⟨268558568728835370028209431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179039045819223580018806287 268558568728835370028209431)
    ·
      refine ⟨402837853093253055042314147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268558568728835370028209431 402837853093253055042314147)
      ·
        refine ⟨604256779639879582563471221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402837853093253055042314147 604256779639879582563471221)
        ·
          refine ⟨56649073091238710865325427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 604256779639879582563471221 56649073091238710865325427)
          ·
            refine ⟨84973609636858066297988141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56649073091238710865325427 84973609636858066297988141)
            ·
              refine ⟨31865103613821774861745553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84973609636858066297988141 31865103613821774861745553)
              ·
                refine ⟨23898827710366331146309165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31865103613821774861745553 23898827710366331146309165)
                ·
                  refine ⟨8962060391387374179865937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23898827710366331146309165 8962060391387374179865937)
                  ·
                    refine ⟨6721545293540530634899453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8962060391387374179865937 6721545293540530634899453)
                    ·
                      refine ⟨2520579485077698988087295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721545293540530634899453 2520579485077698988087295)
                      ·
                        rfl

theorem cell23_4908811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 3, 2, 3, 2, 3].length) (baseStart_4908811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908811 prefixEnd_4908811 := by exact prefixLift 4908811
  have htrace : WordTrace (prefixWord ++ tailWord_4908811) baseStart_4908811 baseEnd_4908811 := by
    simpa [prefixWord, tailWord_4908811, baseEnd_4908811] using wordTrace_append hprefix tailTrace_4908811
  have hstable : (prefixWord ++ tailWord_4908811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908811).length < 2 ^ (prefixWord ++ tailWord_4908811).sum := by decide
  have hdescent : baseEnd_4908811 < baseStart_4908811 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908818 : List Nat := [3, 2, 4, 1, 1, 1, 1, 3, 1, 6]
def baseStart_4908818 : Nat := 118140960795 + 4908818 * 2 ^ 59
def prefixEnd_4908818 : Nat := 4983230072969 + 3 ^ 40 * 4908818 * 2
def baseEnd_4908818 : Nat := 840194359814093486899921

theorem tailTrace_4908818 : CollatzResearch.WordTrace tailWord_4908818 prefixEnd_4908818 840194359814093486899921 := by
  unfold tailWord_4908818
  simp only [CollatzResearch.WordTrace]
  refine ⟨44759825282549555053577777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119359534086798813476207405 44759825282549555053577777)
  ·
    refine ⟨33569868961912166290183333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44759825282549555053577777 33569868961912166290183333)
    ·
      refine ⟨6294350430358531179409375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 33569868961912166290183333 6294350430358531179409375)
      ·
        refine ⟨9441525645537796769114063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294350430358531179409375 9441525645537796769114063)
        ·
          refine ⟨14162288468306695153671095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9441525645537796769114063 14162288468306695153671095)
          ·
            refine ⟨21243432702460042730506643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14162288468306695153671095 21243432702460042730506643)
            ·
              refine ⟨31865149053690064095759965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21243432702460042730506643 31865149053690064095759965)
              ·
                refine ⟨11949430895133774035909987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31865149053690064095759965 11949430895133774035909987)
                ·
                  refine ⟨17924146342700661053864981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11949430895133774035909987 17924146342700661053864981)
                  ·
                    refine ⟨840194359814093486899921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17924146342700661053864981 840194359814093486899921)
                    ·
                      rfl

theorem cell23_4908818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_4908818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908818 prefixEnd_4908818 := by exact prefixLift 4908818
  have htrace : WordTrace (prefixWord ++ tailWord_4908818) baseStart_4908818 baseEnd_4908818 := by
    simpa [prefixWord, tailWord_4908818, baseEnd_4908818] using wordTrace_append hprefix tailTrace_4908818
  have hstable : (prefixWord ++ tailWord_4908818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908818).length < 2 ^ (prefixWord ++ tailWord_4908818).sum := by decide
  have hdescent : baseEnd_4908818 < baseStart_4908818 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908821 : List Nat := [1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 4]
def baseStart_4908821 : Nat := 118140960795 + 4908821 * 2 ^ 59
def prefixEnd_4908821 : Nat := 4983230072969 + 3 ^ 40 * 4908821 * 2
def baseEnd_4908821 : Nat := 2520584619884243948962249

theorem tailTrace_4908821 : CollatzResearch.WordTrace tailWord_4908821 prefixEnd_4908821 2520584619884243948962249 := by
  unfold tailWord_4908821
  simp only [CollatzResearch.WordTrace]
  refine ⟨179039410549187351726670317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119359607032791567817780211 179039410549187351726670317)
  ·
    refine ⟨67139778955945256897501369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179039410549187351726670317 67139778955945256897501369)
    ·
      refine ⟨50354834216958942673126027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67139778955945256897501369 50354834216958942673126027)
      ·
        refine ⟨75532251325438414009689041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50354834216958942673126027 75532251325438414009689041)
        ·
          refine ⟨56649188494078810507266781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75532251325438414009689041 56649188494078810507266781)
          ·
            refine ⟨21243445685279553940225043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56649188494078810507266781 21243445685279553940225043)
            ·
              refine ⟨31865168527919330910337565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21243445685279553940225043 31865168527919330910337565)
              ·
                refine ⟨11949438197969749091376587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31865168527919330910337565 11949438197969749091376587)
                ·
                  refine ⟨17924157296954623637064881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11949438197969749091376587 17924157296954623637064881)
                  ·
                    refine ⟨13443117972715967727798661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17924157296954623637064881 13443117972715967727798661)
                    ·
                      refine ⟨2520584619884243948962249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13443117972715967727798661 2520584619884243948962249)
                      ·
                        rfl

theorem cell23_4908821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 3, 1, 3, 1, 2, 4].length) (baseStart_4908821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908821 prefixEnd_4908821 := by exact prefixLift 4908821
  have htrace : WordTrace (prefixWord ++ tailWord_4908821) baseStart_4908821 baseEnd_4908821 := by
    simpa [prefixWord, tailWord_4908821, baseEnd_4908821] using wordTrace_append hprefix tailTrace_4908821
  have hstable : (prefixWord ++ tailWord_4908821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908821).length < 2 ^ (prefixWord ++ tailWord_4908821).sum := by decide
  have hdescent : baseEnd_4908821 < baseStart_4908821 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908828 : List Nat := [2, 2, 3, 1, 1, 2, 2, 4, 1, 2, 3]
def baseStart_4908828 : Nat := 118140960795 + 4908828 * 2 ^ 59
def prefixEnd_4908828 : Nat := 4983230072969 + 3 ^ 40 * 4908828 * 2
def baseEnd_4908828 : Nat := 2520588214248825421574717

theorem tailTrace_4908828 : CollatzResearch.WordTrace tailWord_4908828 prefixEnd_4908828 2520588214248825421574717 := by
  unfold tailWord_4908828
  simp only [CollatzResearch.WordTrace]
  refine ⟨89519832930080995961087569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119359777240107994614783425 89519832930080995961087569)
  ·
    refine ⟨67139874697560746970815677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89519832930080995961087569 67139874697560746970815677)
    ·
      refine ⟨25177453011585280114055879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67139874697560746970815677 25177453011585280114055879)
      ·
        refine ⟨37766179517377920171083819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25177453011585280114055879 37766179517377920171083819)
        ·
          refine ⟨56649269276066880256625729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37766179517377920171083819 56649269276066880256625729)
          ·
            refine ⟨42486951957050160192469297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56649269276066880256625729 42486951957050160192469297)
            ·
              refine ⟨31865213967787620144351973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42486951957050160192469297 31865213967787620144351973)
              ·
                refine ⟨5974727618960178777065995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31865213967787620144351973 5974727618960178777065995)
                ·
                  refine ⟨8962091428440268165598993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974727618960178777065995 8962091428440268165598993)
                  ·
                    refine ⟨6721568571330201124199245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8962091428440268165598993 6721568571330201124199245)
                    ·
                      refine ⟨2520588214248825421574717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721568571330201124199245 2520588214248825421574717)
                      ·
                        rfl

theorem cell23_4908828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 4, 1, 2, 3].length) (baseStart_4908828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908828 prefixEnd_4908828 := by exact prefixLift 4908828
  have htrace : WordTrace (prefixWord ++ tailWord_4908828) baseStart_4908828 baseEnd_4908828 := by
    simpa [prefixWord, tailWord_4908828, baseEnd_4908828] using wordTrace_append hprefix tailTrace_4908828
  have hstable : (prefixWord ++ tailWord_4908828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908828).length < 2 ^ (prefixWord ++ tailWord_4908828).sum := by decide
  have hdescent : baseEnd_4908828 < baseStart_4908828 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908831 : List Nat := [1, 1, 2, 4, 2, 1, 5, 7]
def baseStart_4908831 : Nat := 118140960795 + 4908831 * 2 ^ 59
def prefixEnd_4908831 : Nat := 4983230072969 + 3 ^ 40 * 4908831 * 2
def baseEnd_4908831 : Nat := 93355176099658848512489

theorem tailTrace_4908831 : CollatzResearch.WordTrace tailWord_4908831 prefixEnd_4908831 93355176099658848512489 := by
  unfold tailWord_4908831
  simp only [CollatzResearch.WordTrace]
  refine ⟨179039775279151123434534347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119359850186100748956356231 179039775279151123434534347)
  ·
    refine ⟨268559662918726685151801521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179039775279151123434534347 268559662918726685151801521)
    ·
      refine ⟨201419747189045013863851141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268559662918726685151801521 201419747189045013863851141)
      ·
        refine ⟨37766202597945940099472089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 201419747189045013863851141 37766202597945940099472089)
        ·
          refine ⟨28324651948459455074604067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37766202597945940099472089 28324651948459455074604067)
          ·
            refine ⟨42486977922689182611906101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28324651948459455074604067 42486977922689182611906101)
            ·
              refine ⟨3983154180252110869866197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 42486977922689182611906101 3983154180252110869866197)
              ·
                refine ⟨93355176099658848512489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3983154180252110869866197 93355176099658848512489)
                ·
                  rfl

theorem cell23_4908831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 5, 7].length) (baseStart_4908831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908831 prefixEnd_4908831 := by exact prefixLift 4908831
  have htrace : WordTrace (prefixWord ++ tailWord_4908831) baseStart_4908831 baseEnd_4908831 := by
    simpa [prefixWord, tailWord_4908831, baseEnd_4908831] using wordTrace_append hprefix tailTrace_4908831
  have hstable : (prefixWord ++ tailWord_4908831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908831).length < 2 ^ (prefixWord ++ tailWord_4908831).sum := by decide
  have hdescent : baseEnd_4908831 < baseStart_4908831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908852 : List Nat := [2, 5, 1, 1, 2, 3, 1, 2, 2, 4]
def baseStart_4908852 : Nat := 118140960795 + 4908852 * 2 ^ 59
def prefixEnd_4908852 : Nat := 4983230072969 + 3 ^ 40 * 4908852 * 2
def baseEnd_4908852 : Nat := 840200179261511109224869

theorem tailTrace_4908852 : CollatzResearch.WordTrace tailWord_4908852 prefixEnd_4908852 840200179261511109224869 := by
  unfold tailWord_4908852
  simp only [CollatzResearch.WordTrace]
  refine ⟨89520270606037522010524405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119360360808050029347365873 89520270606037522010524405)
  ·
    refine ⟨8392525369316017688486663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89520270606037522010524405 8392525369316017688486663)
    ·
      refine ⟨12588788053974026532729995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8392525369316017688486663 12588788053974026532729995)
      ·
        refine ⟨18883182080961039799094993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12588788053974026532729995 18883182080961039799094993)
        ·
          refine ⟨14162386560720779849321245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18883182080961039799094993 14162386560720779849321245)
          ·
            refine ⟨5310894960270292443495467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14162386560720779849321245 5310894960270292443495467)
            ·
              refine ⟨7966342440405438665243201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5310894960270292443495467 7966342440405438665243201)
              ·
                refine ⟨5974756830304078998932401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7966342440405438665243201 5974756830304078998932401)
                ·
                  refine ⟨4481067622728059249199301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974756830304078998932401 4481067622728059249199301)
                  ·
                    refine ⟨840200179261511109224869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481067622728059249199301 840200179261511109224869)
                    ·
                      rfl

theorem cell23_4908852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 1, 2, 2, 4].length) (baseStart_4908852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908852 prefixEnd_4908852 := by exact prefixLift 4908852
  have htrace : WordTrace (prefixWord ++ tailWord_4908852) baseStart_4908852 baseEnd_4908852 := by
    simpa [prefixWord, tailWord_4908852, baseEnd_4908852] using wordTrace_append hprefix tailTrace_4908852
  have hstable : (prefixWord ++ tailWord_4908852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908852).length < 2 ^ (prefixWord ++ tailWord_4908852).sum := by decide
  have hdescent : baseEnd_4908852 < baseStart_4908852 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908885 : List Nat := [1, 3, 2, 2, 2, 2, 1, 4, 1, 3, 2]
def baseStart_4908885 : Nat := 118140960795 + 4908885 * 2 ^ 59
def prefixEnd_4908885 : Nat := 4983230072969 + 3 ^ 40 * 4908885 * 2
def baseEnd_4908885 : Nat := 2520617482646131698561955

theorem tailTrace_4908885 : CollatzResearch.WordTrace tailWord_4908885 prefixEnd_4908885 2520617482646131698561955 := by
  unfold tailWord_4908885
  simp only [CollatzResearch.WordTrace]
  refine ⟨179041744820955490657000109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119361163213970327104666739 179041744820955490657000109)
  ·
    refine ⟨67140654307858308996375041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179041744820955490657000109 67140654307858308996375041)
    ·
      refine ⟨50355490730893731747281281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67140654307858308996375041 50355490730893731747281281)
      ·
        refine ⟨37766618048170298810460961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50355490730893731747281281 37766618048170298810460961)
        ·
          refine ⟨28324963536127724107845721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37766618048170298810460961 28324963536127724107845721)
          ·
            refine ⟨21243722652095793080884291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28324963536127724107845721 21243722652095793080884291)
            ·
              refine ⟨31865583978143689621326437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21243722652095793080884291 31865583978143689621326437)
              ·
                refine ⟨5974796995901941803998707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 31865583978143689621326437 5974796995901941803998707)
                ·
                  refine ⟨8962195493852912705998061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5974796995901941803998707 8962195493852912705998061)
                  ·
                    refine ⟨3360823310194842264749273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8962195493852912705998061 3360823310194842264749273)
                    ·
                      refine ⟨2520617482646131698561955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360823310194842264749273 2520617482646131698561955)
                      ·
                        rfl

theorem cell23_4908885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 2, 1, 4, 1, 3, 2].length) (baseStart_4908885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908885 prefixEnd_4908885 := by exact prefixLift 4908885
  have htrace : WordTrace (prefixWord ++ tailWord_4908885) baseStart_4908885 baseEnd_4908885 := by
    simpa [prefixWord, tailWord_4908885, baseEnd_4908885] using wordTrace_append hprefix tailTrace_4908885
  have hstable : (prefixWord ++ tailWord_4908885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908885).length < 2 ^ (prefixWord ++ tailWord_4908885).sum := by decide
  have hdescent : baseEnd_4908885 < baseStart_4908885 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908901 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 3]
def baseStart_4908901 : Nat := 118140960795 + 4908901 * 2 ^ 59
def prefixEnd_4908901 : Nat := 4983230072969 + 3 ^ 40 * 4908901 * 2
def baseEnd_4908901 : Nat := 2520625698336603635961881

theorem tailTrace_4908901 : CollatzResearch.WordTrace tailWord_4908901 prefixEnd_4908901 2520625698336603635961881 := by
  unfold tailWord_4908901
  simp only [CollatzResearch.WordTrace]
  refine ⟨179042328388897525389582557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119361552259265016926388371 179042328388897525389582557)
  ·
    refine ⟨67140873145836572021093459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179042328388897525389582557 67140873145836572021093459)
    ·
      refine ⟨100711309718754858031640189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67140873145836572021093459 100711309718754858031640189)
      ·
        refine ⟨37766741144533071761865071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100711309718754858031640189 37766741144533071761865071)
        ·
          refine ⟨56650111716799607642797607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37766741144533071761865071 56650111716799607642797607)
          ·
            refine ⟨84975167575199411464196411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56650111716799607642797607 84975167575199411464196411)
            ·
              refine ⟨127462751362799117196294617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84975167575199411464196411 127462751362799117196294617)
              ·
                refine ⟨95597063522099337897220963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127462751362799117196294617 95597063522099337897220963)
                ·
                  refine ⟨143395595283149006845831445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95597063522099337897220963 143395595283149006845831445)
                  ·
                    refine ⟨6721668528897609695898349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 143395595283149006845831445 6721668528897609695898349)
                    ·
                      refine ⟨2520625698336603635961881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721668528897609695898349 2520625698336603635961881)
                      ·
                        rfl

theorem cell23_4908901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 6, 3].length) (baseStart_4908901 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908901 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908901 prefixEnd_4908901 := by exact prefixLift 4908901
  have htrace : WordTrace (prefixWord ++ tailWord_4908901) baseStart_4908901 baseEnd_4908901 := by
    simpa [prefixWord, tailWord_4908901, baseEnd_4908901] using wordTrace_append hprefix tailTrace_4908901
  have hstable : (prefixWord ++ tailWord_4908901).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908901).length < 2 ^ (prefixWord ++ tailWord_4908901).sum := by decide
  have hdescent : baseEnd_4908901 < baseStart_4908901 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908915 : List Nat := [1, 1, 1, 2, 2, 1, 3, 6, 2, 2, 2]
def baseStart_4908915 : Nat := 118140960795 + 4908915 * 2 ^ 59
def prefixEnd_4908915 : Nat := 4983230072969 + 3 ^ 40 * 4908915 * 2
def baseEnd_4908915 : Nat := 2520632887065766581186817

theorem tailTrace_4908915 : CollatzResearch.WordTrace tailWord_4908915 prefixEnd_4908915 2520632887065766581186817 := by
  unfold tailWord_4908915
  simp only [CollatzResearch.WordTrace]
  refine ⟨179042839010846805780592199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119361892673897870520394799 179042839010846805780592199)
  ·
    refine ⟨268564258516270208670888299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179042839010846805780592199 268564258516270208670888299)
    ·
      refine ⟨402846387774405313006332449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268564258516270208670888299 402846387774405313006332449)
      ·
        refine ⟨302134790830803984754749337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402846387774405313006332449 302134790830803984754749337)
        ·
          refine ⟨226601093123102988566062003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302134790830803984754749337 226601093123102988566062003)
          ·
            refine ⟨339901639684654482849093005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226601093123102988566062003 339901639684654482849093005)
            ·
              refine ⟨127463114881745431068409877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339901639684654482849093005 127463114881745431068409877)
              ·
                refine ⟨5974833510081817081331713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 127463114881745431068409877 5974833510081817081331713)
                ·
                  refine ⟨4481125132561362810998785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974833510081817081331713 4481125132561362810998785)
                  ·
                    refine ⟨3360843849421022108249089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481125132561362810998785 3360843849421022108249089)
                    ·
                      refine ⟨2520632887065766581186817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360843849421022108249089 2520632887065766581186817)
                      ·
                        rfl

theorem cell23_4908915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 3, 6, 2, 2, 2].length) (baseStart_4908915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908915 prefixEnd_4908915 := by exact prefixLift 4908915
  have htrace : WordTrace (prefixWord ++ tailWord_4908915) baseStart_4908915 baseEnd_4908915 := by
    simpa [prefixWord, tailWord_4908915, baseEnd_4908915] using wordTrace_append hprefix tailTrace_4908915
  have hstable : (prefixWord ++ tailWord_4908915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908915).length < 2 ^ (prefixWord ++ tailWord_4908915).sum := by decide
  have hdescent : baseEnd_4908915 < baseStart_4908915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4908926 : List Nat := [4, 2, 3, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_4908926 : Nat := 118140960795 + 4908926 * 2 ^ 59
def prefixEnd_4908926 : Nat := 4983230072969 + 3 ^ 40 * 4908926 * 2
def baseEnd_4908926 : Nat := 2520638535352966038149267

theorem tailTrace_4908926 : CollatzResearch.WordTrace tailWord_4908926 prefixEnd_4908926 2520638535352966038149267 := by
  unfold tailWord_4908926
  simp only [CollatzResearch.WordTrace]
  refine ⟨22380405026725869332405329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119362160142537969772828421 22380405026725869332405329)
  ·
    refine ⟨16785303770044401999303997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22380405026725869332405329 16785303770044401999303997)
    ·
      refine ⟨6294488913766650749738999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 16785303770044401999303997 6294488913766650749738999)
      ·
        refine ⟨9441733370649976124608499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6294488913766650749738999 9441733370649976124608499)
        ·
          refine ⟨14162600055974964186912749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9441733370649976124608499 14162600055974964186912749)
          ·
            refine ⟨5310975020990611570092281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14162600055974964186912749 5310975020990611570092281)
            ·
              refine ⟨3983231265742958677569211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5310975020990611570092281 3983231265742958677569211)
              ·
                refine ⟨5974846898614438016353817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983231265742958677569211 5974846898614438016353817)
                ·
                  refine ⟨4481135173960828512265363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5974846898614438016353817 4481135173960828512265363)
                  ·
                    refine ⟨6721702760941242768398045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4481135173960828512265363 6721702760941242768398045)
                    ·
                      refine ⟨2520638535352966038149267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721702760941242768398045 2520638535352966038149267)
                      ·
                        rfl

theorem cell23_4908926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_4908926 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4908926 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4908926 prefixEnd_4908926 := by exact prefixLift 4908926
  have htrace : WordTrace (prefixWord ++ tailWord_4908926) baseStart_4908926 baseEnd_4908926 := by
    simpa [prefixWord, tailWord_4908926, baseEnd_4908926] using wordTrace_append hprefix tailTrace_4908926
  have hstable : (prefixWord ++ tailWord_4908926).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4908926).length < 2 ^ (prefixWord ++ tailWord_4908926).sum := by decide
  have hdescent : baseEnd_4908926 < baseStart_4908926 := by decide
  rcases family_descends (prefixWord ++ tailWord_4908926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909001 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 4]
def baseStart_4909001 : Nat := 118140960795 + 4909001 * 2 ^ 59
def prefixEnd_4909001 : Nat := 4983230072969 + 3 ^ 40 * 4909001 * 2
def baseEnd_4909001 : Nat := 2520677046402053244711421

theorem tailTrace_4909001 : CollatzResearch.WordTrace tailWord_4909001 prefixEnd_4909001 2520677046402053244711421 := by
  unfold tailWord_4909001
  simp only [CollatzResearch.WordTrace]
  refine ⟨179045975688535242468222857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119363983792356828312148571 179045975688535242468222857)
  ·
    refine ⟨134284481766401431851167143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179045975688535242468222857 134284481766401431851167143)
    ·
      refine ⟨201426722649602147776750715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134284481766401431851167143 201426722649602147776750715)
      ·
        refine ⟨302140083974403221665126073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201426722649602147776750715 302140083974403221665126073)
        ·
          refine ⟨226605062980802416248844555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302140083974403221665126073 226605062980802416248844555)
          ·
            refine ⟨339907594471203624373266833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226605062980802416248844555 339907594471203624373266833)
            ·
              refine ⟨254930695853402718279950125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339907594471203624373266833 254930695853402718279950125)
              ·
                refine ⟨95599010945026019354981297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 254930695853402718279950125 95599010945026019354981297)
                ·
                  refine ⟨71699258208769514516235973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95599010945026019354981297 71699258208769514516235973)
                  ·
                    refine ⟨13443610914144283971794245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 71699258208769514516235973 13443610914144283971794245)
                    ·
                      refine ⟨2520677046402053244711421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13443610914144283971794245 2520677046402053244711421)
                      ·
                        rfl

theorem cell23_4909001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 2, 4, 4].length) (baseStart_4909001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909001 prefixEnd_4909001 := by exact prefixLift 4909001
  have htrace : WordTrace (prefixWord ++ tailWord_4909001) baseStart_4909001 baseEnd_4909001 := by
    simpa [prefixWord, tailWord_4909001, baseEnd_4909001] using wordTrace_append hprefix tailTrace_4909001
  have hstable : (prefixWord ++ tailWord_4909001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909001).length < 2 ^ (prefixWord ++ tailWord_4909001).sum := by decide
  have hdescent : baseEnd_4909001 < baseStart_4909001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909051 : List Nat := [1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7]
def baseStart_4909051 : Nat := 118140960795 + 4909051 * 2 ^ 59
def prefixEnd_4909051 : Nat := 4983230072969 + 3 ^ 40 * 4909051 * 2
def baseEnd_4909051 : Nat := 2520702720434778049086191

theorem tailTrace_4909051 : CollatzResearch.WordTrace tailWord_4909051 prefixEnd_4909051 2520702720434778049086191 := by
  unfold tailWord_4909051
  simp only [CollatzResearch.WordTrace]
  refine ⟨179047799338354101007543007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119365199558902734005028671 179047799338354101007543007)
  ·
    refine ⟨268571699007531151511314511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179047799338354101007543007 268571699007531151511314511)
    ·
      refine ⟨402857548511296727266971767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268571699007531151511314511 402857548511296727266971767)
      ·
        refine ⟨604286322766945090900457651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402857548511296727266971767 604286322766945090900457651)
        ·
          refine ⟨906429484150417636350686477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604286322766945090900457651 906429484150417636350686477)
          ·
            refine ⟨339911056556406613631507429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906429484150417636350686477 339911056556406613631507429)
            ·
              refine ⟨63733323104326240055907643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 339911056556406613631507429 63733323104326240055907643)
              ·
                refine ⟨95599984656489360083861465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 63733323104326240055907643 95599984656489360083861465)
                ·
                  refine ⟨71699988492367020062896099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95599984656489360083861465 71699988492367020062896099)
                  ·
                    refine ⟨107549982738550530094344149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71699988492367020062896099 107549982738550530094344149)
                    ·
                      refine ⟨2520702720434778049086191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107549982738550530094344149 2520702720434778049086191)
                      ·
                        rfl

theorem cell23_4909051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 4, 1, 2, 1, 7].length) (baseStart_4909051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909051 prefixEnd_4909051 := by exact prefixLift 4909051
  have htrace : WordTrace (prefixWord ++ tailWord_4909051) baseStart_4909051 baseEnd_4909051 := by
    simpa [prefixWord, tailWord_4909051, baseEnd_4909051] using wordTrace_append hprefix tailTrace_4909051
  have hstable : (prefixWord ++ tailWord_4909051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909051).length < 2 ^ (prefixWord ++ tailWord_4909051).sum := by decide
  have hdescent : baseEnd_4909051 < baseStart_4909051 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909066 : List Nat := [3, 1, 2, 2, 5, 1, 1, 3, 1, 4]
def baseStart_4909066 : Nat := 118140960795 + 4909066 * 2 ^ 59
def prefixEnd_4909066 : Nat := 4983230072969 + 3 ^ 40 * 4909066 * 2
def baseEnd_4909066 : Nat := 840236807548198496799541

theorem tailTrace_4909066 : CollatzResearch.WordTrace tailWord_4909066 prefixEnd_4909066 840236807548198496799541 := by
  unfold tailWord_4909066
  simp only [CollatzResearch.WordTrace]
  refine ⟨44762086608324939642334763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119365564288866505712892701 44762086608324939642334763)
  ·
    refine ⟨67143129912487409463502145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44762086608324939642334763 67143129912487409463502145)
    ·
      refine ⟨50357347434365557097626609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67143129912487409463502145 50357347434365557097626609)
      ·
        refine ⟨37768010575774167823219957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50357347434365557097626609 37768010575774167823219957)
        ·
          refine ⟨3540750991478828233426871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37768010575774167823219957 3540750991478828233426871)
          ·
            refine ⟨5311126487218242350140307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540750991478828233426871 5311126487218242350140307)
            ·
              refine ⟨7966689730827363525210461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311126487218242350140307 7966689730827363525210461)
              ·
                refine ⟨2987508649060261321953923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7966689730827363525210461 2987508649060261321953923)
                ·
                  refine ⟨4481262973590391982930885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987508649060261321953923 4481262973590391982930885)
                  ·
                    refine ⟨840236807548198496799541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481262973590391982930885 840236807548198496799541)
                    ·
                      rfl

theorem cell23_4909066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 5, 1, 1, 3, 1, 4].length) (baseStart_4909066 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909066 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909066 prefixEnd_4909066 := by exact prefixLift 4909066
  have htrace : WordTrace (prefixWord ++ tailWord_4909066) baseStart_4909066 baseEnd_4909066 := by
    simpa [prefixWord, tailWord_4909066, baseEnd_4909066] using wordTrace_append hprefix tailTrace_4909066
  have hstable : (prefixWord ++ tailWord_4909066).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909066).length < 2 ^ (prefixWord ++ tailWord_4909066).sum := by decide
  have hdescent : baseEnd_4909066 < baseStart_4909066 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909082 : List Nat := [3, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2]
def baseStart_4909082 : Nat := 118140960795 + 4909082 * 2 ^ 59
def prefixEnd_4909082 : Nat := 4983230072969 + 3 ^ 40 * 4909082 * 2
def baseEnd_4909082 : Nat := 2520718638335067427798549

theorem tailTrace_4909082 : CollatzResearch.WordTrace tailWord_4909082 prefixEnd_4909082 2520718638335067427798549 := by
  unfold tailWord_4909082
  simp only [CollatzResearch.WordTrace]
  refine ⟨44762232500310448325480375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119365953334161195534614333 44762232500310448325480375)
  ·
    refine ⟨67143348750465672488220563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44762232500310448325480375 67143348750465672488220563)
    ·
      refine ⟨100715023125698508732330845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67143348750465672488220563 100715023125698508732330845)
      ·
        refine ⟨37768133672136940774624067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100715023125698508732330845 37768133672136940774624067)
        ·
          refine ⟨56652200508205411161936101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37768133672136940774624067 56652200508205411161936101)
          ·
            refine ⟨10622287595288514592863019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56652200508205411161936101 10622287595288514592863019)
            ·
              refine ⟨15933431392932771889294529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10622287595288514592863019 15933431392932771889294529)
              ·
                refine ⟨11950073544699578916970897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15933431392932771889294529 11950073544699578916970897)
                ·
                  refine ⟨8962555158524684187728173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11950073544699578916970897 8962555158524684187728173)
                  ·
                    refine ⟨3360958184446756570398065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8962555158524684187728173 3360958184446756570398065)
                    ·
                      refine ⟨2520718638335067427798549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360958184446756570398065 2520718638335067427798549)
                      ·
                        rfl

theorem cell23_4909082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 4, 1, 2, 2, 3, 2].length) (baseStart_4909082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909082 prefixEnd_4909082 := by exact prefixLift 4909082
  have htrace : WordTrace (prefixWord ++ tailWord_4909082) baseStart_4909082 baseEnd_4909082 := by
    simpa [prefixWord, tailWord_4909082, baseEnd_4909082] using wordTrace_append hprefix tailTrace_4909082
  have hstable : (prefixWord ++ tailWord_4909082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909082).length < 2 ^ (prefixWord ++ tailWord_4909082).sum := by decide
  have hdescent : baseEnd_4909082 < baseStart_4909082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909089 : List Nat := [1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 3]
def baseStart_4909089 : Nat := 118140960795 + 4909089 * 2 ^ 59
def prefixEnd_4909089 : Nat := 4983230072969 + 3 ^ 40 * 4909089 * 2
def baseEnd_4909089 : Nat := 2520722232699648900411017

theorem tailTrace_4909089 : CollatzResearch.WordTrace tailWord_4909089 prefixEnd_4909089 2520722232699648900411017 := by
  unfold tailWord_4909089
  simp only [CollatzResearch.WordTrace]
  refine ⟨179049185312216433497426321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119366123541477622331617547 179049185312216433497426321)
  ·
    refine ⟨134286888984162325123069741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179049185312216433497426321 134286888984162325123069741)
    ·
      refine ⟨50357583369060871921151153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134286888984162325123069741 50357583369060871921151153)
      ·
        refine ⟨37768187526795653940863365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50357583369060871921151153 37768187526795653940863365)
        ·
          refine ⟨7081535161274185113911881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 37768187526795653940863365 7081535161274185113911881)
          ·
            refine ⟨5311151370955638835433911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7081535161274185113911881 5311151370955638835433911)
            ·
              refine ⟨7966727056433458253150867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311151370955638835433911 7966727056433458253150867)
              ·
                refine ⟨11950090584650187379726301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7966727056433458253150867 11950090584650187379726301)
                ·
                  refine ⟨4481283969243820267397363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11950090584650187379726301 4481283969243820267397363)
                  ·
                    refine ⟨6721925953865730401096045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4481283969243820267397363 6721925953865730401096045)
                    ·
                      refine ⟨2520722232699648900411017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6721925953865730401096045 2520722232699648900411017)
                      ·
                        rfl

theorem cell23_4909089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 1, 3, 1, 3].length) (baseStart_4909089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909089 prefixEnd_4909089 := by exact prefixLift 4909089
  have htrace : WordTrace (prefixWord ++ tailWord_4909089) baseStart_4909089 baseEnd_4909089 := by
    simpa [prefixWord, tailWord_4909089, baseEnd_4909089] using wordTrace_append hprefix tailTrace_4909089
  have hstable : (prefixWord ++ tailWord_4909089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909089).length < 2 ^ (prefixWord ++ tailWord_4909089).sum := by decide
  have hdescent : baseEnd_4909089 < baseStart_4909089 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909096 : List Nat := [2, 1, 5, 3, 2, 1, 2, 1, 6]
def baseStart_4909096 : Nat := 118140960795 + 4909096 * 2 ^ 59
def prefixEnd_4909096 : Nat := 4983230072969 + 3 ^ 40 * 4909096 * 2
def baseEnd_4909096 : Nat := 280080647451581152558165

theorem tailTrace_4909096 : CollatzResearch.WordTrace tailWord_4909096 prefixEnd_4909096 280080647451581152558165 := by
  unfold tailWord_4909096
  simp only [CollatzResearch.WordTrace]
  refine ⟨89524720311595536846465571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119366293748794049128620761 89524720311595536846465571)
  ·
    refine ⟨134287080467393305269698357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89524720311595536846465571 134287080467393305269698357)
    ·
      refine ⟨12589413793818122369034221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134287080467393305269698357 12589413793818122369034221)
      ·
        refine ⟨4721030172681795888387833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12589413793818122369034221 4721030172681795888387833)
        ·
          refine ⟨3540772629511346916290875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4721030172681795888387833 3540772629511346916290875)
          ·
            refine ⟨5311158944267020374436313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3540772629511346916290875 5311158944267020374436313)
            ·
              refine ⟨3983369208200265280827235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311158944267020374436313 3983369208200265280827235)
              ·
                refine ⟨5975053812300397921240853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983369208200265280827235 5975053812300397921240853)
                ·
                  refine ⟨280080647451581152558165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5975053812300397921240853 280080647451581152558165)
                  ·
                    rfl

theorem cell23_4909096_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 2, 1, 6].length) (baseStart_4909096 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909096 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909096 prefixEnd_4909096 := by exact prefixLift 4909096
  have htrace : WordTrace (prefixWord ++ tailWord_4909096) baseStart_4909096 baseEnd_4909096 := by
    simpa [prefixWord, tailWord_4909096, baseEnd_4909096] using wordTrace_append hprefix tailTrace_4909096
  have hstable : (prefixWord ++ tailWord_4909096).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909096).length < 2 ^ (prefixWord ++ tailWord_4909096).sum := by decide
  have hdescent : baseEnd_4909096 < baseStart_4909096 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909096) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909129 : List Nat := [1, 2, 1, 1, 2, 2, 4, 5, 1, 2, 2]
def baseStart_4909129 : Nat := 118140960795 + 4909129 * 2 ^ 59
def prefixEnd_4909129 : Nat := 4983230072969 + 3 ^ 40 * 4909129 * 2
def baseEnd_4909129 : Nat := 2520742771925828743910833

theorem tailTrace_4909129 : CollatzResearch.WordTrace tailWord_4909129 prefixEnd_4909129 2520742771925828743910833 := by
  unfold tailWord_4909129
  simp only [CollatzResearch.WordTrace]
  refine ⟨179050644232071520328882441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119367096154714346885921627 179050644232071520328882441)
  ·
    refine ⟨134287983174053640246661831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179050644232071520328882441 134287983174053640246661831)
    ·
      refine ⟨201431974761080460369992747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134287983174053640246661831 201431974761080460369992747)
      ·
        refine ⟨302147962141620690554989121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201431974761080460369992747 302147962141620690554989121)
        ·
          refine ⟨226610971606215517916241841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302147962141620690554989121 226610971606215517916241841)
          ·
            refine ⟨169958228704661638437181381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226610971606215517916241841 169958228704661638437181381)
            ·
              refine ⟨31867167882124057206971509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 169958228704661638437181381 31867167882124057206971509)
              ·
                refine ⟨2987546988949130363153579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 31867167882124057206971509 2987546988949130363153579)
                ·
                  refine ⟨4481320483423695544730369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987546988949130363153579 4481320483423695544730369)
                  ·
                    refine ⟨3360990362567771658547777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481320483423695544730369 3360990362567771658547777)
                    ·
                      refine ⟨2520742771925828743910833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3360990362567771658547777 2520742771925828743910833)
                      ·
                        rfl

theorem cell23_4909129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 4, 5, 1, 2, 2].length) (baseStart_4909129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909129 prefixEnd_4909129 := by exact prefixLift 4909129
  have htrace : WordTrace (prefixWord ++ tailWord_4909129) baseStart_4909129 baseEnd_4909129 := by
    simpa [prefixWord, tailWord_4909129, baseEnd_4909129] using wordTrace_append hprefix tailTrace_4909129
  have hstable : (prefixWord ++ tailWord_4909129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909129).length < 2 ^ (prefixWord ++ tailWord_4909129).sum := by decide
  have hdescent : baseEnd_4909129 < baseStart_4909129 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909189 : List Nat := [1, 3, 1, 1, 5, 2, 1, 3, 1, 3, 2]
def baseStart_4909189 : Nat := 118140960795 + 4909189 * 2 ^ 59
def prefixEnd_4909189 : Nat := 4983230072969 + 3 ^ 40 * 4909189 * 2
def baseEnd_4909189 : Nat := 2520773580765098509160557

theorem tailTrace_4909189 : CollatzResearch.WordTrace tailWord_4909189 prefixEnd_4909189 2520773580765098509160557 := by
  unfold tailWord_4909189
  simp only [CollatzResearch.WordTrace]
  refine ⟨179052832611854150576066621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119368555074569433717377747 179052832611854150576066621)
  ·
    refine ⟨67144812229445306466024983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179052832611854150576066621 67144812229445306466024983)
    ·
      refine ⟨100717218344167959699037475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67144812229445306466024983 100717218344167959699037475)
      ·
        refine ⟨151075827516251939548556213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100717218344167959699037475 151075827516251939548556213)
        ·
          refine ⟨14163358829648619332677145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151075827516251939548556213 14163358829648619332677145)
          ·
            refine ⟨10622519122236464499507859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14163358829648619332677145 10622519122236464499507859)
            ·
              refine ⟨15933778683354696749261789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10622519122236464499507859 15933778683354696749261789)
              ·
                refine ⟨5975167006258011280973171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15933778683354696749261789 5975167006258011280973171)
                ·
                  refine ⟨8962750509387016921459757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975167006258011280973171 8962750509387016921459757)
                  ·
                    refine ⟨3361031441020131345547409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8962750509387016921459757 3361031441020131345547409)
                    ·
                      refine ⟨2520773580765098509160557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361031441020131345547409 2520773580765098509160557)
                      ·
                        rfl

theorem cell23_4909189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 1, 3, 1, 3, 2].length) (baseStart_4909189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909189 prefixEnd_4909189 := by exact prefixLift 4909189
  have htrace : WordTrace (prefixWord ++ tailWord_4909189) baseStart_4909189 baseEnd_4909189 := by
    simpa [prefixWord, tailWord_4909189, baseEnd_4909189] using wordTrace_append hprefix tailTrace_4909189
  have hstable : (prefixWord ++ tailWord_4909189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909189).length < 2 ^ (prefixWord ++ tailWord_4909189).sum := by decide
  have hdescent : baseEnd_4909189 < baseStart_4909189 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909228 : List Nat := [2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 6]
def baseStart_4909228 : Nat := 118140960795 + 4909228 * 2 ^ 59
def prefixEnd_4909228 : Nat := 4983230072969 + 3 ^ 40 * 4909228 * 2
def baseEnd_4909228 : Nat := 2520793606510623856572877

theorem tailTrace_4909228 : CollatzResearch.WordTrace tailWord_4909228 prefixEnd_4909228 2520793606510623856572877 := by
  unfold tailWord_4909228
  simp only [CollatzResearch.WordTrace]
  refine ⟨89527127529356430118368169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119369503372475240157824225 89527127529356430118368169)
  ·
    refine ⟨67145345647017322588776127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89527127529356430118368169 67145345647017322588776127)
    ·
      refine ⟨100718018470525983883164191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67145345647017322588776127 100718018470525983883164191)
      ·
        refine ⟨151077027705788975824746287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100718018470525983883164191 151077027705788975824746287)
        ·
          refine ⟨226615541558683463737119431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151077027705788975824746287 226615541558683463737119431)
          ·
            refine ⟨339923312338025195605679147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226615541558683463737119431 339923312338025195605679147)
            ·
              refine ⟨509884968507037793408518721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339923312338025195605679147 509884968507037793408518721)
              ·
                refine ⟨382413726380278345056389041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509884968507037793408518721 382413726380278345056389041)
                ·
                  refine ⟨286810294785208758792291781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 382413726380278345056389041 286810294785208758792291781)
                  ·
                    refine ⟨53776930272226642273554709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 286810294785208758792291781 53776930272226642273554709)
                    ·
                      refine ⟨2520793606510623856572877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53776930272226642273554709 2520793606510623856572877)
                      ·
                        rfl

theorem cell23_4909228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 6].length) (baseStart_4909228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909228 prefixEnd_4909228 := by exact prefixLift 4909228
  have htrace : WordTrace (prefixWord ++ tailWord_4909228) baseStart_4909228 baseEnd_4909228 := by
    simpa [prefixWord, tailWord_4909228, baseEnd_4909228] using wordTrace_append hprefix tailTrace_4909228
  have hstable : (prefixWord ++ tailWord_4909228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909228).length < 2 ^ (prefixWord ++ tailWord_4909228).sum := by decide
  have hdescent : baseEnd_4909228 < baseStart_4909228 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909242 : List Nat := [3, 1, 1, 1, 2, 2, 5, 3, 5]
def baseStart_4909242 : Nat := 118140960795 + 4909242 * 2 ^ 59
def prefixEnd_4909242 : Nat := 4983230072969 + 3 ^ 40 * 4909242 * 2
def baseEnd_4909242 : Nat := 280088977248865200199757

theorem tailTrace_4909242 : CollatzResearch.WordTrace tailWord_4909242 prefixEnd_4909242 280088977248865200199757 := by
  unfold tailWord_4909242
  simp only [CollatzResearch.WordTrace]
  refine ⟨44763691420165535156936495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119369843787108093751830653 44763691420165535156936495)
  ·
    refine ⟨67145537130248302735404743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44763691420165535156936495 67145537130248302735404743)
    ·
      refine ⟨100718305695372454103107115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67145537130248302735404743 100718305695372454103107115)
      ·
        refine ⟨151077458543058681154660673, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100718305695372454103107115 151077458543058681154660673)
        ·
          refine ⟨113308093907294010865995505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151077458543058681154660673 113308093907294010865995505)
          ·
            refine ⟨84981070430470508149496629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113308093907294010865995505 84981070430470508149496629)
            ·
              refine ⟨7966975352856610139015309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84981070430470508149496629 7966975352856610139015309)
              ·
                refine ⟨2987615757321228802130741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7966975352856610139015309 2987615757321228802130741)
                ·
                  refine ⟨280088977248865200199757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987615757321228802130741 280088977248865200199757)
                  ·
                    rfl

theorem cell23_4909242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 5, 3, 5].length) (baseStart_4909242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909242 prefixEnd_4909242 := by exact prefixLift 4909242
  have htrace : WordTrace (prefixWord ++ tailWord_4909242) baseStart_4909242 baseEnd_4909242 := by
    simpa [prefixWord, tailWord_4909242, baseEnd_4909242] using wordTrace_append hprefix tailTrace_4909242
  have hstable : (prefixWord ++ tailWord_4909242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909242).length < 2 ^ (prefixWord ++ tailWord_4909242).sum := by decide
  have hdescent : baseEnd_4909242 < baseStart_4909242 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909270 : List Nat := [5, 2, 1, 2, 1, 1, 4, 1, 2, 2, 2]
def baseStart_4909270 : Nat := 118140960795 + 4909270 * 2 ^ 59
def prefixEnd_4909270 : Nat := 4983230072969 + 3 ^ 40 * 4909270 * 2
def baseEnd_4909270 : Nat := 2520815172698112692247685

theorem tailTrace_4909270 : CollatzResearch.WordTrace tailWord_4909270 prefixEnd_4909270 2520815172698112692247685 := by
  unfold tailWord_4909270
  simp only [CollatzResearch.WordTrace]
  refine ⟨11190986682785043838110329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119370524616373800939843509 11190986682785043838110329)
  ·
    refine ⟨8393240012088782878582747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11190986682785043838110329 8393240012088782878582747)
    ·
      refine ⟨12589860018133174317874121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393240012088782878582747 12589860018133174317874121)
      ·
        refine ⟨9442395013599880738405591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12589860018133174317874121 9442395013599880738405591)
        ·
          refine ⟨14163592520399821107608387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9442395013599880738405591 14163592520399821107608387)
          ·
            refine ⟨21245388780599731661412581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14163592520399821107608387 21245388780599731661412581)
            ·
              refine ⟨3983510396362449686514859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21245388780599731661412581 3983510396362449686514859)
              ·
                refine ⟨5975265594543674529772289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983510396362449686514859 5975265594543674529772289)
                ·
                  refine ⟨4481449195907755897329217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5975265594543674529772289 4481449195907755897329217)
                  ·
                    refine ⟨3361086896930816922996913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481449195907755897329217 3361086896930816922996913)
                    ·
                      refine ⟨2520815172698112692247685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361086896930816922996913 2520815172698112692247685)
                      ·
                        rfl

theorem cell23_4909270_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 4, 1, 2, 2, 2].length) (baseStart_4909270 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909270 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909270 prefixEnd_4909270 := by exact prefixLift 4909270
  have htrace : WordTrace (prefixWord ++ tailWord_4909270) baseStart_4909270 baseEnd_4909270 := by
    simpa [prefixWord, tailWord_4909270, baseEnd_4909270] using wordTrace_append hprefix tailTrace_4909270
  have hstable : (prefixWord ++ tailWord_4909270).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909270).length < 2 ^ (prefixWord ++ tailWord_4909270).sum := by decide
  have hdescent : baseEnd_4909270 < baseStart_4909270 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909270) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909292 : List Nat := [2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 4]
def baseStart_4909292 : Nat := 118140960795 + 4909292 * 2 ^ 59
def prefixEnd_4909292 : Nat := 4983230072969 + 3 ^ 40 * 4909292 * 2
def baseEnd_4909292 : Nat := 2520826469272511606172583

theorem tailTrace_4909292 : CollatzResearch.WordTrace tailWord_4909292 prefixEnd_4909292 2520826469272511606172583 := by
  unfold tailWord_4909292
  simp only [CollatzResearch.WordTrace]
  refine ⟨89528294665240499583533065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119371059553653999444710753 89528294665240499583533065)
  ·
    refine ⟨67146220998930374687649799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89528294665240499583533065 67146220998930374687649799)
    ·
      refine ⟨100719331498395562031474699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67146220998930374687649799 100719331498395562031474699)
      ·
        refine ⟨151078997247593343047212049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100719331498395562031474699 151078997247593343047212049)
        ·
          refine ⟨113309247935695007285409037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151078997247593343047212049 113309247935695007285409037)
          ·
            refine ⟨42490967975885627732028389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113309247935695007285409037 42490967975885627732028389)
            ·
              refine ⟨7967056495478555199755323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42490967975885627732028389 7967056495478555199755323)
              ·
                refine ⟨11950584743217832799632985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967056495478555199755323 11950584743217832799632985)
                ·
                  refine ⟨8962938557413374599724739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11950584743217832799632985 8962938557413374599724739)
                  ·
                    refine ⟨13444407836120061899587109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8962938557413374599724739 13444407836120061899587109)
                    ·
                      refine ⟨2520826469272511606172583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13444407836120061899587109 2520826469272511606172583)
                      ·
                        rfl

theorem cell23_4909292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 4].length) (baseStart_4909292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909292 prefixEnd_4909292 := by exact prefixLift 4909292
  have htrace : WordTrace (prefixWord ++ tailWord_4909292) baseStart_4909292 baseEnd_4909292 := by
    simpa [prefixWord, tailWord_4909292, baseEnd_4909292] using wordTrace_append hprefix tailTrace_4909292
  have hstable : (prefixWord ++ tailWord_4909292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909292).length < 2 ^ (prefixWord ++ tailWord_4909292).sum := by decide
  have hdescent : baseEnd_4909292 < baseStart_4909292 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909312 : List Nat := [2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3]
def baseStart_4909312 : Nat := 118140960795 + 4909312 * 2 ^ 59
def prefixEnd_4909312 : Nat := 4983230072969 + 3 ^ 40 * 4909312 * 2
def baseEnd_4909312 : Nat := 2520836738885601527922491

theorem tailTrace_4909312 : CollatzResearch.WordTrace tailWord_4909312 prefixEnd_4909312 2520836738885601527922491 := by
  unfold tailWord_4909312
  simp only [CollatzResearch.WordTrace]
  refine ⟨89528659395204271291397095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119371545860272361721862793 89528659395204271291397095)
  ·
    refine ⟨134292989092806406937095643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89528659395204271291397095 134292989092806406937095643)
    ·
      refine ⟨201439483639209610405643465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134292989092806406937095643 201439483639209610405643465)
      ·
        refine ⟨151079612729407207804232599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201439483639209610405643465 151079612729407207804232599)
        ·
          refine ⟨226619419094110811706348899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151079612729407207804232599 226619419094110811706348899)
          ·
            refine ⟨339929128641166217559523349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226619419094110811706348899 339929128641166217559523349)
            ·
              refine ⟨15934177905054666448102657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 339929128641166217559523349 15934177905054666448102657)
              ·
                refine ⟨11950633428790999836076993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15934177905054666448102657 11950633428790999836076993)
                ·
                  refine ⟨8962975071593249877057745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11950633428790999836076993 8962975071593249877057745)
                  ·
                    refine ⟨6722231303694937407793309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8962975071593249877057745 6722231303694937407793309)
                    ·
                      refine ⟨2520836738885601527922491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6722231303694937407793309 2520836738885601527922491)
                      ·
                        rfl

theorem cell23_4909312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 6, 2, 2, 2, 3].length) (baseStart_4909312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909312 prefixEnd_4909312 := by exact prefixLift 4909312
  have htrace : WordTrace (prefixWord ++ tailWord_4909312) baseStart_4909312 baseEnd_4909312 := by
    simpa [prefixWord, tailWord_4909312, baseEnd_4909312] using wordTrace_append hprefix tailTrace_4909312
  have hstable : (prefixWord ++ tailWord_4909312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909312).length < 2 ^ (prefixWord ++ tailWord_4909312).sum := by decide
  have hdescent : baseEnd_4909312 < baseStart_4909312 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909346 : List Nat := [3, 3, 1, 1, 3, 3, 1, 1, 2, 2, 3]
def baseStart_4909346 : Nat := 118140960795 + 4909346 * 2 ^ 59
def prefixEnd_4909346 : Nat := 4983230072969 + 3 ^ 40 * 4909346 * 2
def baseEnd_4909346 : Nat := 2520854197227854394897335

theorem tailTrace_4909346 : CollatzResearch.WordTrace tailWord_4909346 prefixEnd_4909346 2520854197227854394897335 := by
  unfold tailWord_4909346
  simp only [CollatzResearch.WordTrace]
  refine ⟨44764639718071341597382973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119372372581523577593021261 44764639718071341597382973)
  ·
    refine ⟨16786739894276753099018615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44764639718071341597382973 16786739894276753099018615)
    ·
      refine ⟨25180109841415129648527923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16786739894276753099018615 25180109841415129648527923)
      ·
        refine ⟨37770164762122694472791885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25180109841415129648527923 37770164762122694472791885)
        ·
          refine ⟨14163811785796010427296957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37770164762122694472791885 14163811785796010427296957)
          ·
            refine ⟨5311429419673503910236359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14163811785796010427296957 5311429419673503910236359)
            ·
              refine ⟨7967144129510255865354539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311429419673503910236359 7967144129510255865354539)
              ·
                refine ⟨11950716194265383798031809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967144129510255865354539 11950716194265383798031809)
                ·
                  refine ⟨8963037145699037848523857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11950716194265383798031809 8963037145699037848523857)
                  ·
                    refine ⟨6722277859274278386392893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8963037145699037848523857 6722277859274278386392893)
                    ·
                      refine ⟨2520854197227854394897335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6722277859274278386392893 2520854197227854394897335)
                      ·
                        rfl

theorem cell23_4909346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 3, 1, 1, 2, 2, 3].length) (baseStart_4909346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909346 prefixEnd_4909346 := by exact prefixLift 4909346
  have htrace : WordTrace (prefixWord ++ tailWord_4909346) baseStart_4909346 baseEnd_4909346 := by
    simpa [prefixWord, tailWord_4909346, baseEnd_4909346] using wordTrace_append hprefix tailTrace_4909346
  have hstable : (prefixWord ++ tailWord_4909346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909346).length < 2 ^ (prefixWord ++ tailWord_4909346).sum := by decide
  have hdescent : baseEnd_4909346 < baseStart_4909346 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909392 : List Nat := [2, 1, 1, 1, 1, 6, 3, 1, 1, 6]
def baseStart_4909392 : Nat := 118140960795 + 4909392 * 2 ^ 59
def prefixEnd_4909392 : Nat := 4983230072969 + 3 ^ 40 * 4909392 * 2
def baseEnd_4909392 : Nat := 840292605779320404974041

theorem tailTrace_4909392 : CollatzResearch.WordTrace tailWord_4909392 prefixEnd_4909392 840292605779320404974041 := by
  unfold tailWord_4909392
  simp only [CollatzResearch.WordTrace]
  refine ⟨89530118315059358122853215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119373491086745810830470953 89530118315059358122853215)
  ·
    refine ⟨134295177472589037184279823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89530118315059358122853215 134295177472589037184279823)
    ·
      refine ⟨201442766208883555776419735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134295177472589037184279823 201442766208883555776419735)
      ·
        refine ⟨302164149313325333664629603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201442766208883555776419735 302164149313325333664629603)
        ·
          refine ⟨453246223969988000496944405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 302164149313325333664629603 453246223969988000496944405)
          ·
            refine ⟨21245916748593187523294269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 453246223969988000496944405 21245916748593187523294269)
            ·
              refine ⟨7967218780722445321235351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21245916748593187523294269 7967218780722445321235351)
              ·
                refine ⟨11950828171083667981853027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967218780722445321235351 11950828171083667981853027)
                ·
                  refine ⟨17926242256625501972779541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11950828171083667981853027 17926242256625501972779541)
                  ·
                    refine ⟨840292605779320404974041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17926242256625501972779541 840292605779320404974041)
                    ·
                      rfl

theorem cell23_4909392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 3, 1, 1, 6].length) (baseStart_4909392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909392 prefixEnd_4909392 := by exact prefixLift 4909392
  have htrace : WordTrace (prefixWord ++ tailWord_4909392) baseStart_4909392 baseEnd_4909392 := by
    simpa [prefixWord, tailWord_4909392, baseEnd_4909392] using wordTrace_append hprefix tailTrace_4909392
  have hstable : (prefixWord ++ tailWord_4909392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909392).length < 2 ^ (prefixWord ++ tailWord_4909392).sum := by decide
  have hdescent : baseEnd_4909392 < baseStart_4909392 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909399 : List Nat := [1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 4]
def baseStart_4909399 : Nat := 118140960795 + 4909399 * 2 ^ 59
def prefixEnd_4909399 : Nat := 4983230072969 + 3 ^ 40 * 4909399 * 2
def baseEnd_4909399 : Nat := 2520881411702542687534591

theorem tailTrace_4909399 : CollatzResearch.WordTrace tailWord_4909399 prefixEnd_4909399 2520881411702542687534591 := by
  unfold tailWord_4909399
  simp only [CollatzResearch.WordTrace]
  refine ⟨179060491941093356441211251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119373661294062237627474167 179060491941093356441211251)
  ·
    refine ⟨268590737911640034661816877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179060491941093356441211251 268590737911640034661816877)
    ·
      refine ⟨100721526716865012998181329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268590737911640034661816877 100721526716865012998181329)
      ·
        refine ⟨75541145037648759748635997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100721526716865012998181329 75541145037648759748635997)
        ·
          refine ⟨28327929389118284905738499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75541145037648759748635997 28327929389118284905738499)
          ·
            refine ⟨42491894083677427358607749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28327929389118284905738499 42491894083677427358607749)
            ·
              refine ⟨7967230140689517629738953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42491894083677427358607749 7967230140689517629738953)
              ·
                refine ⟨5975422605517138222304215, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7967230140689517629738953 5975422605517138222304215)
                ·
                  refine ⟨8963133908275707333456323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975422605517138222304215 8963133908275707333456323)
                  ·
                    refine ⟨13444700862413561000184485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8963133908275707333456323 13444700862413561000184485)
                    ·
                      refine ⟨2520881411702542687534591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13444700862413561000184485 2520881411702542687534591)
                      ·
                        rfl

theorem cell23_4909399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_4909399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909399 prefixEnd_4909399 := by exact prefixLift 4909399
  have htrace : WordTrace (prefixWord ++ tailWord_4909399) baseStart_4909399 baseEnd_4909399 := by
    simpa [prefixWord, tailWord_4909399, baseEnd_4909399] using wordTrace_append hprefix tailTrace_4909399
  have hstable : (prefixWord ++ tailWord_4909399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909399).length < 2 ^ (prefixWord ++ tailWord_4909399).sum := by decide
  have hdescent : baseEnd_4909399 < baseStart_4909399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909410 : List Nat := [3, 3, 2, 1, 1, 4, 1, 3, 1, 1, 3]
def baseStart_4909410 : Nat := 118140960795 + 4909410 * 2 ^ 59
def prefixEnd_4909410 : Nat := 4983230072969 + 3 ^ 40 * 4909410 * 2
def baseEnd_4909410 : Nat := 2520887059989742144497041

theorem tailTrace_4909410 : CollatzResearch.WordTrace tailWord_4909410 prefixEnd_4909410 2520887059989742144497041 := by
  unfold tailWord_4909410
  simp only [CollatzResearch.WordTrace]
  refine ⟨44765223286013376329965421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119373928762702336879907789 44765223286013376329965421)
  ·
    refine ⟨16786958732255016123737033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44765223286013376329965421 16786958732255016123737033)
    ·
      refine ⟨12590219049191262092802775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16786958732255016123737033 12590219049191262092802775)
      ·
        refine ⟨18885328573786893139204163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12590219049191262092802775 18885328573786893139204163)
        ·
          refine ⟨28327992860680339708806245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18885328573786893139204163 28327992860680339708806245)
          ·
            refine ⟨5311498661377563695401171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28327992860680339708806245 5311498661377563695401171)
            ·
              refine ⟨7967247992066345543101757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311498661377563695401171 7967247992066345543101757)
              ·
                refine ⟨2987717997024879578663159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7967247992066345543101757 2987717997024879578663159)
                ·
                  refine ⟨4481576995537319367994739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2987717997024879578663159 4481576995537319367994739)
                  ·
                    refine ⟨6722365493305979051992109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4481576995537319367994739 6722365493305979051992109)
                    ·
                      refine ⟨2520887059989742144497041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6722365493305979051992109 2520887059989742144497041)
                      ·
                        rfl

theorem cell23_4909410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 4, 1, 3, 1, 1, 3].length) (baseStart_4909410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909410 prefixEnd_4909410 := by exact prefixLift 4909410
  have htrace : WordTrace (prefixWord ++ tailWord_4909410) baseStart_4909410 baseEnd_4909410 := by
    simpa [prefixWord, tailWord_4909410, baseEnd_4909410] using wordTrace_append hprefix tailTrace_4909410
  have hstable : (prefixWord ++ tailWord_4909410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909410).length < 2 ^ (prefixWord ++ tailWord_4909410).sum := by decide
  have hdescent : baseEnd_4909410 < baseStart_4909410 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909412 : List Nat := [2, 3, 1, 1, 3, 1, 2, 1, 3, 2, 4]
def baseStart_4909412 : Nat := 118140960795 + 4909412 * 2 ^ 59
def prefixEnd_4909412 : Nat := 4983230072969 + 3 ^ 40 * 4909412 * 2
def baseEnd_4909412 : Nat := 2520888086951051136672031

theorem tailTrace_4909412 : CollatzResearch.WordTrace tailWord_4909412 prefixEnd_4909412 2520888086951051136672031 := by
  unfold tailWord_4909412
  simp only [CollatzResearch.WordTrace]
  refine ⟨89530483045023129830717245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119373977393364173107622993 89530483045023129830717245)
  ·
    refine ⟨33573931141883673686518967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89530483045023129830717245 33573931141883673686518967)
    ·
      refine ⟨50360896712825510529778451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33573931141883673686518967 50360896712825510529778451)
      ·
        refine ⟨75541345069238265794667677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50360896712825510529778451 75541345069238265794667677)
        ·
          refine ⟨28328004400964349673000379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75541345069238265794667677 28328004400964349673000379)
          ·
            refine ⟨42492006601446524509500569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28328004400964349673000379 42492006601446524509500569)
            ·
              refine ⟨31869004951084893382125427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42492006601446524509500569 31869004951084893382125427)
              ·
                refine ⟨47803507426627340073188141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31869004951084893382125427 47803507426627340073188141)
                ·
                  refine ⟨17926315284985252527445553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47803507426627340073188141 17926315284985252527445553)
                  ·
                    refine ⟨13444736463738939395584165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 17926315284985252527445553 13444736463738939395584165)
                    ·
                      refine ⟨2520888086951051136672031, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13444736463738939395584165 2520888086951051136672031)
                      ·
                        rfl

theorem cell23_4909412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_4909412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909412 prefixEnd_4909412 := by exact prefixLift 4909412
  have htrace : WordTrace (prefixWord ++ tailWord_4909412) baseStart_4909412 baseEnd_4909412 := by
    simpa [prefixWord, tailWord_4909412, baseEnd_4909412] using wordTrace_append hprefix tailTrace_4909412
  have hstable : (prefixWord ++ tailWord_4909412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909412).length < 2 ^ (prefixWord ++ tailWord_4909412).sum := by decide
  have hdescent : baseEnd_4909412 < baseStart_4909412 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909443 : List Nat := [1, 1, 1, 3, 6, 2, 2, 1, 2, 4]
def baseStart_4909443 : Nat := 118140960795 + 4909443 * 2 ^ 59
def prefixEnd_4909443 : Nat := 4983230072969 + 3 ^ 40 * 4909443 * 2
def baseEnd_4909443 : Nat := 840301334950446838461463

theorem tailTrace_4909443 : CollatzResearch.WordTrace tailWord_4909443 prefixEnd_4909443 840301334950446838461463 := by
  unfold tailWord_4909443
  simp only [CollatzResearch.WordTrace]
  refine ⟨179062096752933951955812983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119374731168622634637208655 179062096752933951955812983)
  ·
    refine ⟨268593145129400927933719475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179062096752933951955812983 268593145129400927933719475)
    ·
      refine ⟨402889717694101391900579213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268593145129400927933719475 402889717694101391900579213)
      ·
        refine ⟨151083644135288021962717205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 402889717694101391900579213 151083644135288021962717205)
        ·
          refine ⟨7082045818841626029502369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 151083644135288021962717205 7082045818841626029502369)
          ·
            refine ⟨5311534364131219522126777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7082045818841626029502369 5311534364131219522126777)
            ·
              refine ⟨3983650773098414641595083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311534364131219522126777 3983650773098414641595083)
              ·
                refine ⟨5975476159647621962392625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983650773098414641595083 5975476159647621962392625)
                ·
                  refine ⟨4481607119735716471794469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5975476159647621962392625 4481607119735716471794469)
                  ·
                    refine ⟨840301334950446838461463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4481607119735716471794469 840301334950446838461463)
                    ·
                      rfl

theorem cell23_4909443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 6, 2, 2, 1, 2, 4].length) (baseStart_4909443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909443 prefixEnd_4909443 := by exact prefixLift 4909443
  have htrace : WordTrace (prefixWord ++ tailWord_4909443) baseStart_4909443 baseEnd_4909443 := by
    simpa [prefixWord, tailWord_4909443, baseEnd_4909443] using wordTrace_append hprefix tailTrace_4909443
  have hstable : (prefixWord ++ tailWord_4909443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909443).length < 2 ^ (prefixWord ++ tailWord_4909443).sum := by decide
  have hdescent : baseEnd_4909443 < baseStart_4909443 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909450 : List Nat := [3, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4]
def baseStart_4909450 : Nat := 118140960795 + 4909450 * 2 ^ 59
def prefixEnd_4909450 : Nat := 4983230072969 + 3 ^ 40 * 4909450 * 2
def baseEnd_4909450 : Nat := 2520907599215921987996857

theorem tailTrace_4909450 : CollatzResearch.WordTrace tailWord_4909450 prefixEnd_4909450 2520907599215921987996857 := by
  unfold tailWord_4909450
  simp only [CollatzResearch.WordTrace]
  refine ⟨44765588015977148037829451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119374901375939061434211869 44765588015977148037829451)
  ·
    refine ⟨67148382023965722056744177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44765588015977148037829451 67148382023965722056744177)
    ·
      refine ⟨50361286517974291542558133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67148382023965722056744177 50361286517974291542558133)
      ·
        refine ⟨4721370611060089832114825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 50361286517974291542558133 4721370611060089832114825)
        ·
          refine ⟨3541027958295067374086119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4721370611060089832114825 3541027958295067374086119)
          ·
            refine ⟨5311541937442601061129179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541027958295067374086119 5311541937442601061129179)
            ·
              refine ⟨7967312906163901591693769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311541937442601061129179 7967312906163901591693769)
              ·
                refine ⟨5975484679622926193770327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7967312906163901591693769 5975484679622926193770327)
                ·
                  refine ⟨8963227019434389290655491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975484679622926193770327 8963227019434389290655491)
                  ·
                    refine ⟨13444840529151583935983237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8963227019434389290655491 13444840529151583935983237)
                    ·
                      refine ⟨2520907599215921987996857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13444840529151583935983237 2520907599215921987996857)
                      ·
                        rfl

theorem cell23_4909450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_4909450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909450 prefixEnd_4909450 := by exact prefixLift 4909450
  have htrace : WordTrace (prefixWord ++ tailWord_4909450) baseStart_4909450 baseEnd_4909450 := by
    simpa [prefixWord, tailWord_4909450, baseEnd_4909450] using wordTrace_append hprefix tailTrace_4909450
  have hstable : (prefixWord ++ tailWord_4909450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909450).length < 2 ^ (prefixWord ++ tailWord_4909450).sum := by decide
  have hdescent : baseEnd_4909450 < baseStart_4909450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909470 : List Nat := [4, 3, 1, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_4909470 : Nat := 118140960795 + 4909470 * 2 ^ 59
def prefixEnd_4909470 : Nat := 4983230072969 + 3 ^ 40 * 4909470 * 2
def baseEnd_4909470 : Nat := 2520917868829011909746765

theorem tailTrace_4909470 : CollatzResearch.WordTrace tailWord_4909470 prefixEnd_4909470 2520917868829011909746765 := by
  unfold tailWord_4909470
  simp only [CollatzResearch.WordTrace]
  refine ⟨22382885190479516945880733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119375387682557423711363909 22382885190479516945880733)
  ·
    refine ⟨8393581946429818854705275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22382885190479516945880733 8393581946429818854705275)
    ·
      refine ⟨12590372919644728282057913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8393581946429818854705275 12590372919644728282057913)
      ·
        refine ⟨9442779689733546211543435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12590372919644728282057913 9442779689733546211543435)
        ·
          refine ⟨14164169534600319317315153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9442779689733546211543435 14164169534600319317315153)
          ·
            refine ⟨10623127150950239487986365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14164169534600319317315153 10623127150950239487986365)
            ·
              refine ⟨3983672681606339807994887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10623127150950239487986365 3983672681606339807994887)
              ·
                refine ⟨5975509022409509711992331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983672681606339807994887 5975509022409509711992331)
                ·
                  refine ⟨8963263533614264567988497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975509022409509711992331 8963263533614264567988497)
                  ·
                    refine ⟨6722447650210698425991373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8963263533614264567988497 6722447650210698425991373)
                    ·
                      refine ⟨2520917868829011909746765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6722447650210698425991373 2520917868829011909746765)
                      ·
                        rfl

theorem cell23_4909470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_4909470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909470 prefixEnd_4909470 := by exact prefixLift 4909470
  have htrace : WordTrace (prefixWord ++ tailWord_4909470) baseStart_4909470 baseEnd_4909470 := by
    simpa [prefixWord, tailWord_4909470, baseEnd_4909470] using wordTrace_append hprefix tailTrace_4909470
  have hstable : (prefixWord ++ tailWord_4909470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909470).length < 2 ^ (prefixWord ++ tailWord_4909470).sum := by decide
  have hdescent : baseEnd_4909470 < baseStart_4909470 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909476 : List Nat := [2, 3, 1, 2, 1, 1, 2, 5, 1, 3, 2]
def baseStart_4909476 : Nat := 118140960795 + 4909476 * 2 ^ 59
def prefixEnd_4909476 : Nat := 4983230072969 + 3 ^ 40 * 4909476 * 2
def baseEnd_4909476 : Nat := 2520920949712938886271737

theorem tailTrace_4909476 : CollatzResearch.WordTrace tailWord_4909476 prefixEnd_4909476 2520920949712938886271737 := by
  unfold tailWord_4909476
  simp only [CollatzResearch.WordTrace]
  refine ⟨89531650180907199295882141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119375533574542932394509521 89531650180907199295882141)
  ·
    refine ⟨33574368817840199735955803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89531650180907199295882141 33574368817840199735955803)
    ·
      refine ⟨50361553226760299603933705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33574368817840199735955803 50361553226760299603933705)
      ·
        refine ⟨37771164920070224702950279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50361553226760299603933705 37771164920070224702950279)
        ·
          refine ⟨56656747380105337054425419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37771164920070224702950279 56656747380105337054425419)
          ·
            refine ⟨84985121070158005581638129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56656747380105337054425419 84985121070158005581638129)
            ·
              refine ⟨63738840802618504186228597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 84985121070158005581638129 63738840802618504186228597)
              ·
                refine ⟨5975516325245484767458931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 63738840802618504186228597 5975516325245484767458931)
                ·
                  refine ⟨8963274487868227151188397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975516325245484767458931 8963274487868227151188397)
                  ·
                    refine ⟨3361227932950585181695649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8963274487868227151188397 3361227932950585181695649)
                    ·
                      refine ⟨2520920949712938886271737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361227932950585181695649 2520920949712938886271737)
                      ·
                        rfl

theorem cell23_4909476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 2, 5, 1, 3, 2].length) (baseStart_4909476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909476 prefixEnd_4909476 := by exact prefixLift 4909476
  have htrace : WordTrace (prefixWord ++ tailWord_4909476) baseStart_4909476 baseEnd_4909476 := by
    simpa [prefixWord, tailWord_4909476, baseEnd_4909476] using wordTrace_append hprefix tailTrace_4909476
  have hstable : (prefixWord ++ tailWord_4909476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909476).length < 2 ^ (prefixWord ++ tailWord_4909476).sum := by decide
  have hdescent : baseEnd_4909476 < baseStart_4909476 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909512 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 9]
def baseStart_4909512 : Nat := 118140960795 + 4909512 * 2 ^ 59
def prefixEnd_4909512 : Nat := 4983230072969 + 3 ^ 40 * 4909512 * 2
def baseEnd_4909512 : Nat := 280104381668500082824619

theorem tailTrace_4909512 : CollatzResearch.WordTrace tailWord_4909512 prefixEnd_4909512 280104381668500082824619 := by
  unfold tailWord_4909512
  simp only [CollatzResearch.WordTrace]
  refine ⟨89532306694841988370037395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119376408926455984493383193 89532306694841988370037395)
  ·
    refine ⟨134298460042262982555056093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89532306694841988370037395 134298460042262982555056093)
    ·
      refine ⟨50361922515848618458146035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134298460042262982555056093 50361922515848618458146035)
      ·
        refine ⟨75542883773772927687219053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50361922515848618458146035 75542883773772927687219053)
        ·
          refine ⟨28328581415164847882707145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 75542883773772927687219053 28328581415164847882707145)
          ·
            refine ⟨21246436061373635912030359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28328581415164847882707145 21246436061373635912030359)
            ·
              refine ⟨31869654092060453868045539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21246436061373635912030359 31869654092060453868045539)
              ·
                refine ⟨47804481138090680802068309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31869654092060453868045539 47804481138090680802068309)
                ·
                  refine ⟨280104381668500082824619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 47804481138090680802068309 280104381668500082824619)
                  ·
                    rfl

theorem cell23_4909512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 9].length) (baseStart_4909512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909512 prefixEnd_4909512 := by exact prefixLift 4909512
  have htrace : WordTrace (prefixWord ++ tailWord_4909512) baseStart_4909512 baseEnd_4909512 := by
    simpa [prefixWord, tailWord_4909512, baseEnd_4909512] using wordTrace_append hprefix tailTrace_4909512
  have hstable : (prefixWord ++ tailWord_4909512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909512).length < 2 ^ (prefixWord ++ tailWord_4909512).sum := by decide
  have hdescent : baseEnd_4909512 < baseStart_4909512 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909546 : List Nat := [3, 1, 3, 1, 3, 1, 2, 4, 5]
def baseStart_4909546 : Nat := 118140960795 + 4909546 * 2 ^ 59
def prefixEnd_4909546 : Nat := 4983230072969 + 3 ^ 40 * 4909546 * 2
def baseEnd_4909546 : Nat := 280106321484305956932935

theorem tailTrace_4909546 : CollatzResearch.WordTrace tailWord_4909546 prefixEnd_4909546 280106321484305956932935 := by
  unfold tailWord_4909546
  simp only [CollatzResearch.WordTrace]
  refine ⟨44766463367890200136703123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119377235647707200364541661 44766463367890200136703123)
  ·
    refine ⟨67149695051835300205054685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44766463367890200136703123 67149695051835300205054685)
    ·
      refine ⟨25181135644438237576895507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67149695051835300205054685 25181135644438237576895507)
      ·
        refine ⟨37771703466657356365343261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25181135644438237576895507 37771703466657356365343261)
        ·
          refine ⟨14164388799996508637003723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37771703466657356365343261 14164388799996508637003723)
          ·
            refine ⟨21246583199994762955505585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14164388799996508637003723 21246583199994762955505585)
            ·
              refine ⟨15934937399996072216629189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21246583199994762955505585 15934937399996072216629189)
              ·
                refine ⟨2987800762499263540617973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 15934937399996072216629189 2987800762499263540617973)
                ·
                  refine ⟨280106321484305956932935, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2987800762499263540617973 280106321484305956932935)
                  ·
                    rfl

theorem cell23_4909546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 2, 4, 5].length) (baseStart_4909546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909546 prefixEnd_4909546 := by exact prefixLift 4909546
  have htrace : WordTrace (prefixWord ++ tailWord_4909546) baseStart_4909546 baseEnd_4909546 := by
    simpa [prefixWord, tailWord_4909546, baseEnd_4909546] using wordTrace_append hprefix tailTrace_4909546
  have hstable : (prefixWord ++ tailWord_4909546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909546).length < 2 ^ (prefixWord ++ tailWord_4909546).sum := by decide
  have hdescent : baseEnd_4909546 < baseStart_4909546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909552 : List Nat := [2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7]
def baseStart_4909552 : Nat := 118140960795 + 4909552 * 2 ^ 59
def prefixEnd_4909552 : Nat := 4983230072969 + 3 ^ 40 * 4909552 * 2
def baseEnd_4909552 : Nat := 2520959974242680588921387

theorem tailTrace_4909552 : CollatzResearch.WordTrace tailWord_4909552 prefixEnd_4909552 2520959974242680588921387 := by
  unfold tailWord_4909552
  simp only [CollatzResearch.WordTrace]
  refine ⟨89533036154769531785765455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119377381539692709047687273 89533036154769531785765455)
  ·
    refine ⟨134299554232154297678648183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89533036154769531785765455 134299554232154297678648183)
    ·
      refine ⟨201449331348231446517972275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134299554232154297678648183 201449331348231446517972275)
      ·
        refine ⟨302173997022347169776958413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201449331348231446517972275 302173997022347169776958413)
        ·
          refine ⟨113315248883380188666359405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302173997022347169776958413 113315248883380188666359405)
          ·
            refine ⟨42493218331267570749884777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113315248883380188666359405 42493218331267570749884777)
            ·
              refine ⟨31869913748450678062413583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42493218331267570749884777 31869913748450678062413583)
              ·
                refine ⟨47804870622676017093620375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31869913748450678062413583 47804870622676017093620375)
                ·
                  refine ⟨71707305934014025640430563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47804870622676017093620375 71707305934014025640430563)
                  ·
                    refine ⟨107560958901021038460645845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71707305934014025640430563 107560958901021038460645845)
                    ·
                      refine ⟨2520959974242680588921387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107560958901021038460645845 2520959974242680588921387)
                      ·
                        rfl

theorem cell23_4909552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 2, 1, 1, 1, 7].length) (baseStart_4909552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909552 prefixEnd_4909552 := by exact prefixLift 4909552
  have htrace : WordTrace (prefixWord ++ tailWord_4909552) baseStart_4909552 baseEnd_4909552 := by
    simpa [prefixWord, tailWord_4909552, baseEnd_4909552] using wordTrace_append hprefix tailTrace_4909552
  have hstable : (prefixWord ++ tailWord_4909552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909552).length < 2 ^ (prefixWord ++ tailWord_4909552).sum := by decide
  have hdescent : baseEnd_4909552 < baseStart_4909552 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909557 : List Nat := [1, 3, 5, 1, 3, 1, 1, 1, 1, 4, 2]
def baseStart_4909557 : Nat := 118140960795 + 4909557 * 2 ^ 59
def prefixEnd_4909557 : Nat := 4983230072969 + 3 ^ 40 * 4909557 * 2
def baseEnd_4909557 : Nat := 2520962541645953069358865

theorem tailTrace_4909557 : CollatzResearch.WordTrace tailWord_4909557 prefixEnd_4909557 2520962541645953069358865 := by
  unfold tailWord_4909557
  simp only [CollatzResearch.WordTrace]
  refine ⟨179066254674520949425462925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119377503116347299616975283 179066254674520949425462925)
  ·
    refine ⟨67149845502945356034548597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179066254674520949425462925 67149845502945356034548597)
    ·
      refine ⟨6295298015901127128238931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 67149845502945356034548597 6295298015901127128238931)
      ·
        refine ⟨9442947023851690692358397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6295298015901127128238931 9442947023851690692358397)
        ·
          refine ⟨3541105133944384009634399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9442947023851690692358397 3541105133944384009634399)
          ·
            refine ⟨5311657700916576014451599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541105133944384009634399 5311657700916576014451599)
            ·
              refine ⟨7967486551374864021677399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311657700916576014451599 7967486551374864021677399)
              ·
                refine ⟨11951229827062296032516099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967486551374864021677399 11951229827062296032516099)
                ·
                  refine ⟨17926844740593444048774149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11951229827062296032516099 17926844740593444048774149)
                  ·
                    refine ⟨3361283388861270759145153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17926844740593444048774149 3361283388861270759145153)
                    ·
                      refine ⟨2520962541645953069358865, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361283388861270759145153 2520962541645953069358865)
                      ·
                        rfl

theorem cell23_4909557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 3, 1, 1, 1, 1, 4, 2].length) (baseStart_4909557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909557 prefixEnd_4909557 := by exact prefixLift 4909557
  have htrace : WordTrace (prefixWord ++ tailWord_4909557) baseStart_4909557 baseEnd_4909557 := by
    simpa [prefixWord, tailWord_4909557, baseEnd_4909557] using wordTrace_append hprefix tailTrace_4909557
  have hstable : (prefixWord ++ tailWord_4909557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909557).length < 2 ^ (prefixWord ++ tailWord_4909557).sum := by decide
  have hdescent : baseEnd_4909557 < baseStart_4909557 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909579 : List Nat := [1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4]
def baseStart_4909579 : Nat := 118140960795 + 4909579 * 2 ^ 59
def prefixEnd_4909579 : Nat := 4983230072969 + 3 ^ 40 * 4909579 * 2
def baseEnd_4909579 : Nat := 2520973838220351983283763

theorem tailTrace_4909579 : CollatzResearch.WordTrace tailWord_4909579 prefixEnd_4909579 2520973838220351983283763 := by
  unfold tailWord_4909579
  simp only [CollatzResearch.WordTrace]
  refine ⟨179067057080441247182763791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119378038053627498121842527 179067057080441247182763791)
  ·
    refine ⟨268600585620661870774145687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179067057080441247182763791 268600585620661870774145687)
    ·
      refine ⟨402900878430992806161218531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268600585620661870774145687 402900878430992806161218531)
      ·
        refine ⟨604351317646489209241827797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402900878430992806161218531 604351317646489209241827797)
        ·
          refine ⟨14164484007339590841605339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 604351317646489209241827797 14164484007339590841605339)
          ·
            refine ⟨21246726011009386262408009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14164484007339590841605339 21246726011009386262408009)
            ·
              refine ⟨15935044508257039696806007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21246726011009386262408009 15935044508257039696806007)
              ·
                refine ⟨23902566762385559545209011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15935044508257039696806007 23902566762385559545209011)
                ·
                  refine ⟨35853850143578339317813517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23902566762385559545209011 35853850143578339317813517)
                  ·
                    refine ⟨13445193803841877244180069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 35853850143578339317813517 13445193803841877244180069)
                    ·
                      refine ⟨2520973838220351983283763, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13445193803841877244180069 2520973838220351983283763)
                      ·
                        rfl

theorem cell23_4909579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 2, 1, 1, 3, 4].length) (baseStart_4909579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909579 prefixEnd_4909579 := by exact prefixLift 4909579
  have htrace : WordTrace (prefixWord ++ tailWord_4909579) baseStart_4909579 baseEnd_4909579 := by
    simpa [prefixWord, tailWord_4909579, baseEnd_4909579] using wordTrace_append hprefix tailTrace_4909579
  have hstable : (prefixWord ++ tailWord_4909579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909579).length < 2 ^ (prefixWord ++ tailWord_4909579).sum := by decide
  have hdescent : baseEnd_4909579 < baseStart_4909579 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909596 : List Nat := [2, 2, 3, 1, 2, 3, 1, 2, 2, 1, 4]
def baseStart_4909596 : Nat := 118140960795 + 4909596 * 2 ^ 59
def prefixEnd_4909596 : Nat := 4983230072969 + 3 ^ 40 * 4909596 * 2
def baseEnd_4909596 : Nat := 2520982567391478416771185

theorem tailTrace_4909596 : CollatzResearch.WordTrace tailWord_4909596 prefixEnd_4909596 2520982567391478416771185 := by
  unfold tailWord_4909596
  simp only [CollatzResearch.WordTrace]
  refine ⟨89533838560689829543066321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119378451414253106057421761 89533838560689829543066321)
  ·
    refine ⟨67150378920517372157299741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89533838560689829543066321 67150378920517372157299741)
    ·
      refine ⟨25181392095194014558987403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67150378920517372157299741 25181392095194014558987403)
      ·
        refine ⟨37772088142791021838481105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25181392095194014558987403 37772088142791021838481105)
        ·
          refine ⟨28329066107093266378860829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37772088142791021838481105 28329066107093266378860829)
          ·
            refine ⟨10623399790159974892072811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28329066107093266378860829 10623399790159974892072811)
            ·
              refine ⟨15935099685239962338109217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623399790159974892072811 15935099685239962338109217)
              ·
                refine ⟨11951324763929971753581913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15935099685239962338109217 11951324763929971753581913)
                ·
                  refine ⟨8963493572947478815186435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11951324763929971753581913 8963493572947478815186435)
                  ·
                    refine ⟨13445240359421218222779653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8963493572947478815186435 13445240359421218222779653)
                    ·
                      refine ⟨2520982567391478416771185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13445240359421218222779653 2520982567391478416771185)
                      ·
                        rfl

theorem cell23_4909596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 3, 1, 2, 2, 1, 4].length) (baseStart_4909596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909596 prefixEnd_4909596 := by exact prefixLift 4909596
  have htrace : WordTrace (prefixWord ++ tailWord_4909596) baseStart_4909596 baseEnd_4909596 := by
    simpa [prefixWord, tailWord_4909596, baseEnd_4909596] using wordTrace_append hprefix tailTrace_4909596
  have hstable : (prefixWord ++ tailWord_4909596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909596).length < 2 ^ (prefixWord ++ tailWord_4909596).sum := by decide
  have hdescent : baseEnd_4909596 < baseStart_4909596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909619 : List Nat := [1, 1, 1, 2, 4, 2, 3, 3, 6]
def baseStart_4909619 : Nat := 118140960795 + 4909619 * 2 ^ 59
def prefixEnd_4909619 : Nat := 4983230072969 + 3 ^ 40 * 4909619 * 2
def baseEnd_4909619 : Nat := 280110486382947980753731

theorem tailTrace_4909619 : CollatzResearch.WordTrace tailWord_4909619 prefixEnd_4909619 280110486382947980753731 := by
  unfold tailWord_4909619
  simp only [CollatzResearch.WordTrace]
  refine ⟨179068516000296334014219911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119379010666864222676146607 179068516000296334014219911)
  ·
    refine ⟨268602774000444501021329867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179068516000296334014219911 268602774000444501021329867)
    ·
      refine ⟨402904161000666751531994801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268602774000444501021329867 402904161000666751531994801)
      ·
        refine ⟨302178120750500063648996101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 402904161000666751531994801 302178120750500063648996101)
        ·
          refine ⟨56658397640718761934186769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 302178120750500063648996101 56658397640718761934186769)
          ·
            refine ⟨42493798230539071450640077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56658397640718761934186769 42493798230539071450640077)
            ·
              refine ⟨15935174336452151793990029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42493798230539071450640077 15935174336452151793990029)
              ·
                refine ⟨5975690376169556922746261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15935174336452151793990029 5975690376169556922746261)
                ·
                  refine ⟨280110486382947980753731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5975690376169556922746261 280110486382947980753731)
                  ·
                    rfl

theorem cell23_4909619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 3, 3, 6].length) (baseStart_4909619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909619 prefixEnd_4909619 := by exact prefixLift 4909619
  have htrace : WordTrace (prefixWord ++ tailWord_4909619) baseStart_4909619 baseEnd_4909619 := by
    simpa [prefixWord, tailWord_4909619, baseEnd_4909619] using wordTrace_append hprefix tailTrace_4909619
  have hstable : (prefixWord ++ tailWord_4909619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909619).length < 2 ^ (prefixWord ++ tailWord_4909619).sum := by decide
  have hdescent : baseEnd_4909619 < baseStart_4909619 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909630 : List Nat := [4, 2, 1, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_4909630 : Nat := 118140960795 + 4909630 * 2 ^ 59
def prefixEnd_4909630 : Nat := 4983230072969 + 3 ^ 40 * 4909630 * 2
def baseEnd_4909630 : Nat := 2521000025733731283746029

theorem tailTrace_4909630 : CollatzResearch.WordTrace tailWord_4909630 prefixEnd_4909630 2521000025733731283746029 := by
  unfold tailWord_4909630
  simp only [CollatzResearch.WordTrace]
  refine ⟨22383614650407060361608793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119379278135504321928580229 22383614650407060361608793)
  ·
    refine ⟨16787710987805295271206595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22383614650407060361608793 16787710987805295271206595)
    ·
      refine ⟨25181566481707942906809893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16787710987805295271206595 25181566481707942906809893)
      ·
        refine ⟨4721543715320239295026855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25181566481707942906809893 4721543715320239295026855)
        ·
          refine ⟨7082315572980358942540283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721543715320239295026855 7082315572980358942540283)
          ·
            refine ⟨10623473359470538413810425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082315572980358942540283 10623473359470538413810425)
            ·
              refine ⟨7967605019602903810357819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10623473359470538413810425 7967605019602903810357819)
              ·
                refine ⟨11951407529404355715536729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967605019602903810357819 11951407529404355715536729)
                ·
                  refine ⟨8963555647053266786652547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11951407529404355715536729 8963555647053266786652547)
                  ·
                    refine ⟨13445333470579900179978821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8963555647053266786652547 13445333470579900179978821)
                    ·
                      refine ⟨2521000025733731283746029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13445333470579900179978821 2521000025733731283746029)
                      ·
                        rfl

theorem cell23_4909630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_4909630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909630 prefixEnd_4909630 := by exact prefixLift 4909630
  have htrace : WordTrace (prefixWord ++ tailWord_4909630) baseStart_4909630 baseEnd_4909630 := by
    simpa [prefixWord, tailWord_4909630, baseEnd_4909630] using wordTrace_append hprefix tailTrace_4909630
  have hstable : (prefixWord ++ tailWord_4909630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909630).length < 2 ^ (prefixWord ++ tailWord_4909630).sum := by decide
  have hdescent : baseEnd_4909630 < baseStart_4909630 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909633 : List Nat := [1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 3]
def baseStart_4909633 : Nat := 118140960795 + 4909633 * 2 ^ 59
def prefixEnd_4909633 : Nat := 4983230072969 + 3 ^ 40 * 4909633 * 2
def baseEnd_4909633 : Nat := 2521001566175694772008515

theorem tailTrace_4909633 : CollatzResearch.WordTrace tailWord_4909633 prefixEnd_4909633 2521001566175694772008515 := by
  unfold tailWord_4909633
  simp only [CollatzResearch.WordTrace]
  refine ⟨179069026622245614405229553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119379351081497076270153035 179069026622245614405229553)
  ·
    refine ⟨134301769966684210803922165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179069026622245614405229553 134301769966684210803922165)
    ·
      refine ⟨12590790934376644762867703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 134301769966684210803922165 12590790934376644762867703)
      ·
        refine ⟨18886186401564967144301555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12590790934376644762867703 18886186401564967144301555)
        ·
          refine ⟨28329279602347450716452333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886186401564967144301555 28329279602347450716452333)
          ·
            refine ⟨10623479850880294018669625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28329279602347450716452333 10623479850880294018669625)
            ·
              refine ⟨7967609888160220514002219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10623479850880294018669625 7967609888160220514002219)
              ·
                refine ⟨11951414832240330771003329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967609888160220514002219 11951414832240330771003329)
                ·
                  refine ⟨8963561124180248078252497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11951414832240330771003329 8963561124180248078252497)
                  ·
                    refine ⟨6722670843135186058689373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8963561124180248078252497 6722670843135186058689373)
                    ·
                      refine ⟨2521001566175694772008515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6722670843135186058689373 2521001566175694772008515)
                      ·
                        rfl

theorem cell23_4909633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 2, 1, 2, 2, 3].length) (baseStart_4909633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909633 prefixEnd_4909633 := by exact prefixLift 4909633
  have htrace : WordTrace (prefixWord ++ tailWord_4909633) baseStart_4909633 baseEnd_4909633 := by
    simpa [prefixWord, tailWord_4909633, baseEnd_4909633] using wordTrace_append hprefix tailTrace_4909633
  have hstable : (prefixWord ++ tailWord_4909633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909633).length < 2 ^ (prefixWord ++ tailWord_4909633).sum := by decide
  have hdescent : baseEnd_4909633 < baseStart_4909633 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909679 : List Nat := [1, 1, 2, 1, 3, 2, 3, 3, 1, 6]
def baseStart_4909679 : Nat := 118140960795 + 4909679 * 2 ^ 59
def prefixEnd_4909679 : Nat := 4983230072969 + 3 ^ 40 * 4909679 * 2
def baseEnd_4909679 : Nat := 840341728761933864011101

theorem tailTrace_4909679 : CollatzResearch.WordTrace tailWord_4909679 prefixEnd_4909679 840341728761933864011101 := by
  unfold tailWord_4909679
  simp only [CollatzResearch.WordTrace]
  refine ⟨179070704380078964261404091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119380469586719309507602727 179070704380078964261404091)
  ·
    refine ⟨268606056570118446392106137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179070704380078964261404091 268606056570118446392106137)
    ·
      refine ⟨201454542427588834794079603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268606056570118446392106137 201454542427588834794079603)
      ·
        refine ⟨302181813641383252191119405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201454542427588834794079603 302181813641383252191119405)
        ·
          refine ⟨113318180115518719571669777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302181813641383252191119405 113318180115518719571669777)
          ·
            refine ⟨84988635086639039678752333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113318180115518719571669777 84988635086639039678752333)
            ·
              refine ⟨31870738157489639879532125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 84988635086639039678752333 31870738157489639879532125)
              ·
                refine ⟨11951526809058614954824547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31870738157489639879532125 11951526809058614954824547)
                ·
                  refine ⟨17927290213587922432236821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11951526809058614954824547 17927290213587922432236821)
                  ·
                    refine ⟨840341728761933864011101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17927290213587922432236821 840341728761933864011101)
                    ·
                      rfl

theorem cell23_4909679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 3, 1, 6].length) (baseStart_4909679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909679 prefixEnd_4909679 := by exact prefixLift 4909679
  have htrace : WordTrace (prefixWord ++ tailWord_4909679) baseStart_4909679 baseEnd_4909679 := by
    simpa [prefixWord, tailWord_4909679, baseEnd_4909679] using wordTrace_append hprefix tailTrace_4909679
  have hstable : (prefixWord ++ tailWord_4909679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909679).length < 2 ^ (prefixWord ++ tailWord_4909679).sum := by decide
  have hdescent : baseEnd_4909679 < baseStart_4909679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909700 : List Nat := [2, 3, 2, 1, 3, 3, 2, 1, 1, 5]
def baseStart_4909700 : Nat := 118140960795 + 4909700 * 2 ^ 59
def prefixEnd_4909700 : Nat := 4983230072969 + 3 ^ 40 * 4909700 * 2
def baseEnd_4909700 : Nat := 840345323126515336623569

theorem tailTrace_4909700 : CollatzResearch.WordTrace tailWord_4909700 prefixEnd_4909700 840345323126515336623569 := by
  unfold tailWord_4909700
  simp only [CollatzResearch.WordTrace]
  refine ⟨89535735156501442423959277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119380980208668589898612369 89535735156501442423959277)
  ·
    refine ⟨33575900683688040908984729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89535735156501442423959277 33575900683688040908984729)
    ·
      refine ⟨25181925512766030681738547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 33575900683688040908984729 25181925512766030681738547)
      ·
        refine ⟨37772888269149046022607821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25181925512766030681738547 37772888269149046022607821)
        ·
          refine ⟨14164833100930892258477933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37772888269149046022607821 14164833100930892258477933)
          ·
            refine ⟨5311812412849084596929225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14164833100930892258477933 5311812412849084596929225)
            ·
              refine ⟨3983859309636813447696919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5311812412849084596929225 3983859309636813447696919)
              ·
                refine ⟨5975788964455220171545379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3983859309636813447696919 5975788964455220171545379)
                ·
                  refine ⟨8963683446682830257318069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975788964455220171545379 8963683446682830257318069)
                  ·
                    refine ⟨840345323126515336623569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8963683446682830257318069 840345323126515336623569)
                    ·
                      rfl

theorem cell23_4909700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 3, 2, 1, 1, 5].length) (baseStart_4909700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909700 prefixEnd_4909700 := by exact prefixLift 4909700
  have htrace : WordTrace (prefixWord ++ tailWord_4909700) baseStart_4909700 baseEnd_4909700 := by
    simpa [prefixWord, tailWord_4909700, baseEnd_4909700] using wordTrace_append hprefix tailTrace_4909700
  have hstable : (prefixWord ++ tailWord_4909700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909700).length < 2 ^ (prefixWord ++ tailWord_4909700).sum := by decide
  have hdescent : baseEnd_4909700 < baseStart_4909700 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909703 : List Nat := [1, 1, 4, 2, 1, 2, 1, 2, 5, 2, 2]
def baseStart_4909703 : Nat := 118140960795 + 4909703 * 2 ^ 59
def prefixEnd_4909703 : Nat := 4983230072969 + 3 ^ 40 * 4909703 * 2
def baseEnd_4909703 : Nat := 2521037509821509498133193

theorem tailTrace_4909703 : CollatzResearch.WordTrace tailWord_4909703 prefixEnd_4909703 2521037509821509498133193 := by
  unfold tailWord_4909703
  simp only [CollatzResearch.WordTrace]
  refine ⟨179071579731992016360277763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119381053154661344240185175 179071579731992016360277763)
  ·
    refine ⟨268607369597988024540416645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179071579731992016360277763 268607369597988024540416645)
    ·
      refine ⟨50363881799622754601328121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268607369597988024540416645 50363881799622754601328121)
      ·
        refine ⟨37772911349717065950996091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50363881799622754601328121 37772911349717065950996091)
        ·
          refine ⟨56659367024575598926494137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37772911349717065950996091 56659367024575598926494137)
          ·
            refine ⟨42494525268431699194870603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56659367024575598926494137 42494525268431699194870603)
            ·
              refine ⟨63741787902647548792305905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42494525268431699194870603 63741787902647548792305905)
              ·
                refine ⟨47806340926985661594229429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63741787902647548792305905 47806340926985661594229429)
                ·
                  refine ⟨4481844461904905774459009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 47806340926985661594229429 4481844461904905774459009)
                  ·
                    refine ⟨3361383346428679330844257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481844461904905774459009 3361383346428679330844257)
                    ·
                      refine ⟨2521037509821509498133193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361383346428679330844257 2521037509821509498133193)
                      ·
                        rfl

theorem cell23_4909703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 2, 5, 2, 2].length) (baseStart_4909703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909703 prefixEnd_4909703 := by exact prefixLift 4909703
  have htrace : WordTrace (prefixWord ++ tailWord_4909703) baseStart_4909703 baseEnd_4909703 := by
    simpa [prefixWord, tailWord_4909703, baseEnd_4909703] using wordTrace_append hprefix tailTrace_4909703
  have hstable : (prefixWord ++ tailWord_4909703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909703).length < 2 ^ (prefixWord ++ tailWord_4909703).sum := by decide
  have hdescent : baseEnd_4909703 < baseStart_4909703 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909720 : List Nat := [2, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2]
def baseStart_4909720 : Nat := 118140960795 + 4909720 * 2 ^ 59
def prefixEnd_4909720 : Nat := 4983230072969 + 3 ^ 40 * 4909720 * 2
def baseEnd_4909720 : Nat := 2521046238992635931620615

theorem tailTrace_4909720 : CollatzResearch.WordTrace tailWord_4909720 prefixEnd_4909720 2521046238992635931620615 := by
  unfold tailWord_4909720
  simp only [CollatzResearch.WordTrace]
  refine ⟨89536099886465214131823307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119381466515286952175764409 89536099886465214131823307)
  ·
    refine ⟨134304149829697821197734961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89536099886465214131823307 134304149829697821197734961)
    ·
      refine ⟨100728112372273365898301221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134304149829697821197734961 100728112372273365898301221)
      ·
        refine ⟨18886521069801256105931479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100728112372273365898301221 18886521069801256105931479)
        ·
          refine ⟨28329781604701884158897219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886521069801256105931479 28329781604701884158897219)
          ·
            refine ⟨42494672407052826238345829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28329781604701884158897219 42494672407052826238345829)
            ·
              refine ⟨7967751076322404919689843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 42494672407052826238345829 7967751076322404919689843)
              ·
                refine ⟨11951626614483607379534765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7967751076322404919689843 11951626614483607379534765)
                ·
                  refine ⟨4481859980431352767325537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11951626614483607379534765 4481859980431352767325537)
                  ·
                    refine ⟨3361394985323514575494153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4481859980431352767325537 3361394985323514575494153)
                    ·
                      refine ⟨2521046238992635931620615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361394985323514575494153 2521046238992635931620615)
                      ·
                        rfl

theorem cell23_4909720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 3, 2, 2].length) (baseStart_4909720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909720 prefixEnd_4909720 := by exact prefixLift 4909720
  have htrace : WordTrace (prefixWord ++ tailWord_4909720) baseStart_4909720 baseEnd_4909720 := by
    simpa [prefixWord, tailWord_4909720, baseEnd_4909720] using wordTrace_append hprefix tailTrace_4909720
  have hstable : (prefixWord ++ tailWord_4909720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909720).length < 2 ^ (prefixWord ++ tailWord_4909720).sum := by decide
  have hdescent : baseEnd_4909720 < baseStart_4909720 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909726 : List Nat := [4, 3, 1, 1, 1, 1, 2, 10]
def baseStart_4909726 : Nat := 118140960795 + 4909726 * 2 ^ 59
def prefixEnd_4909726 : Nat := 4983230072969 + 3 ^ 40 * 4909726 * 2
def baseEnd_4909726 : Nat := 93372197032465292894281

theorem tailTrace_4909726 : CollatzResearch.WordTrace tailWord_4909726 prefixEnd_4909726 93372197032465292894281 := by
  unfold tailWord_4909726
  simp only [CollatzResearch.WordTrace]
  refine ⟨22384052326363586411045629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119381612407272460858910021 22384052326363586411045629)
  ·
    refine ⟨8394019622386344904142111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22384052326363586411045629 8394019622386344904142111)
    ·
      refine ⟨12591029433579517356213167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8394019622386344904142111 12591029433579517356213167)
      ·
        refine ⟨18886544150369276034319751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12591029433579517356213167 18886544150369276034319751)
        ·
          refine ⟨28329816225553914051479627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886544150369276034319751 28329816225553914051479627)
          ·
            refine ⟨42494724338330871077219441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28329816225553914051479627 42494724338330871077219441)
            ·
              refine ⟨31871043253748153307914581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42494724338330871077219441 31871043253748153307914581)
              ·
                refine ⟨93372197032465292894281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 31871043253748153307914581 93372197032465292894281)
                ·
                  rfl

theorem cell23_4909726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 2, 10].length) (baseStart_4909726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909726 prefixEnd_4909726 := by exact prefixLift 4909726
  have htrace : WordTrace (prefixWord ++ tailWord_4909726) baseStart_4909726 baseEnd_4909726 := by
    simpa [prefixWord, tailWord_4909726, baseEnd_4909726] using wordTrace_append hprefix tailTrace_4909726
  have hstable : (prefixWord ++ tailWord_4909726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909726).length < 2 ^ (prefixWord ++ tailWord_4909726).sum := by decide
  have hdescent : baseEnd_4909726 < baseStart_4909726 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909796 : List Nat := [2, 3, 1, 1, 1, 4, 1, 2, 2, 1, 5]
def baseStart_4909796 : Nat := 118140960795 + 4909796 * 2 ^ 59
def prefixEnd_4909796 : Nat := 4983230072969 + 3 ^ 40 * 4909796 * 2
def baseEnd_4909796 : Nat := 2521085263522377634270265

theorem tailTrace_4909796 : CollatzResearch.WordTrace tailWord_4909796 prefixEnd_4909796 2521085263522377634270265 := by
  unfold tailWord_4909796
  simp only [CollatzResearch.WordTrace]
  refine ⟨89537485860327546621706621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119383314480436728828942161 89537485860327546621706621)
  ·
    refine ⟨33576557197622829983139983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89537485860327546621706621 33576557197622829983139983)
    ·
      refine ⟨50364835796434244974709975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33576557197622829983139983 50364835796434244974709975)
      ·
        refine ⟨75547253694651367462064963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50364835796434244974709975 75547253694651367462064963)
        ·
          refine ⟨113320880541977051193097445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75547253694651367462064963 113320880541977051193097445)
          ·
            refine ⟨21247665101620697098705771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 113320880541977051193097445 21247665101620697098705771)
            ·
              refine ⟨31871497652431045648058657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21247665101620697098705771 31871497652431045648058657)
              ·
                refine ⟨23903623239323284236043993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31871497652431045648058657 23903623239323284236043993)
                ·
                  refine ⟨17927717429492463177032995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23903623239323284236043993 17927717429492463177032995)
                  ·
                    refine ⟨26891576144238694765549493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17927717429492463177032995 26891576144238694765549493)
                    ·
                      refine ⟨2521085263522377634270265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26891576144238694765549493 2521085263522377634270265)
                      ·
                        rfl

theorem cell23_4909796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_4909796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909796 prefixEnd_4909796 := by exact prefixLift 4909796
  have htrace : WordTrace (prefixWord ++ tailWord_4909796) baseStart_4909796 baseEnd_4909796 := by
    simpa [prefixWord, tailWord_4909796, baseEnd_4909796] using wordTrace_append hprefix tailTrace_4909796
  have hstable : (prefixWord ++ tailWord_4909796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909796).length < 2 ^ (prefixWord ++ tailWord_4909796).sum := by decide
  have hdescent : baseEnd_4909796 < baseStart_4909796 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909797 : List Nat := [1, 3, 1, 4, 1, 4, 1, 2, 1, 3, 2]
def baseStart_4909797 : Nat := 118140960795 + 4909797 * 2 ^ 59
def prefixEnd_4909797 : Nat := 4983230072969 + 3 ^ 40 * 4909797 * 2
def baseEnd_4909797 : Nat := 2521085777003032130357761

theorem tailTrace_4909797 : CollatzResearch.WordTrace tailWord_4909797 prefixEnd_4909797 2521085777003032130357761 := by
  unfold tailWord_4909797
  simp only [CollatzResearch.WordTrace]
  refine ⟨179075008193651470414199645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119383338795767646942799763 179075008193651470414199645)
  ·
    refine ⟨67153128072619301405324867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179075008193651470414199645 67153128072619301405324867)
    ·
      refine ⟨100729692108928952107987301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67153128072619301405324867 100729692108928952107987301)
      ·
        refine ⟨18886817270424178520247619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 100729692108928952107987301 18886817270424178520247619)
        ·
          refine ⟨28330225905636267780371429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886817270424178520247619 28330225905636267780371429)
          ·
            refine ⟨5311917357306800208819643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28330225905636267780371429 5311917357306800208819643)
            ·
              refine ⟨7967876035960200313229465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5311917357306800208819643 7967876035960200313229465)
              ·
                refine ⟨5975907026970150234922099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7967876035960200313229465 5975907026970150234922099)
                ·
                  refine ⟨8963860540455225352383149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5975907026970150234922099 8963860540455225352383149)
                  ·
                    refine ⟨3361447702670709507143681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8963860540455225352383149 3361447702670709507143681)
                    ·
                      refine ⟨2521085777003032130357761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361447702670709507143681 2521085777003032130357761)
                      ·
                        rfl

theorem cell23_4909797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 4, 1, 2, 1, 3, 2].length) (baseStart_4909797 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909797 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909797 prefixEnd_4909797 := by exact prefixLift 4909797
  have htrace : WordTrace (prefixWord ++ tailWord_4909797) baseStart_4909797 baseEnd_4909797 := by
    simpa [prefixWord, tailWord_4909797, baseEnd_4909797] using wordTrace_append hprefix tailTrace_4909797
  have hstable : (prefixWord ++ tailWord_4909797).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909797).length < 2 ^ (prefixWord ++ tailWord_4909797).sum := by decide
  have hdescent : baseEnd_4909797 < baseStart_4909797 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909810 : List Nat := [3, 2, 1, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_4909810 : Nat := 118140960795 + 4909810 * 2 ^ 59
def prefixEnd_4909810 : Nat := 4983230072969 + 3 ^ 40 * 4909810 * 2
def baseEnd_4909810 : Nat := 2521092452251540579495201

theorem tailTrace_4909810 : CollatzResearch.WordTrace tailWord_4909810 prefixEnd_4909810 2521092452251540579495201 := by
  unfold tailWord_4909810
  simp only [CollatzResearch.WordTrace]
  refine ⟨44768870585651093408605721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119383654895069582422948589 44768870585651093408605721)
  ·
    refine ⟨33576652939238320056454291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44768870585651093408605721 33576652939238320056454291)
    ·
      refine ⟨50364979408857480084681437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33576652939238320056454291 50364979408857480084681437)
      ·
        refine ⟨18886867278321555031755539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 50364979408857480084681437 18886867278321555031755539)
        ·
          refine ⟨28330300917482332547633309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18886867278321555031755539 28330300917482332547633309)
          ·
            refine ⟨10623862844055874705362491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28330300917482332547633309 10623862844055874705362491)
            ·
              refine ⟨15935794266083812058043737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10623862844055874705362491 15935794266083812058043737)
              ·
                refine ⟨11951845699562859043532803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15935794266083812058043737 11951845699562859043532803)
                ·
                  refine ⟨17927768549344288565299205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11951845699562859043532803 17927768549344288565299205)
                  ·
                    refine ⟨3361456603002054105993601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17927768549344288565299205 3361456603002054105993601)
                    ·
                      refine ⟨2521092452251540579495201, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361456603002054105993601 2521092452251540579495201)
                      ·
                        rfl

theorem cell23_4909810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_4909810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909810 prefixEnd_4909810 := by exact prefixLift 4909810
  have htrace : WordTrace (prefixWord ++ tailWord_4909810) baseStart_4909810 baseEnd_4909810 := by
    simpa [prefixWord, tailWord_4909810, baseEnd_4909810] using wordTrace_append hprefix tailTrace_4909810
  have hstable : (prefixWord ++ tailWord_4909810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909810).length < 2 ^ (prefixWord ++ tailWord_4909810).sum := by decide
  have hdescent : baseEnd_4909810 < baseStart_4909810 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909819 : List Nat := [1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8]
def baseStart_4909819 : Nat := 118140960795 + 4909819 * 2 ^ 59
def prefixEnd_4909819 : Nat := 4983230072969 + 3 ^ 40 * 4909819 * 2
def baseEnd_4909819 : Nat := 2521097073577431044282659

theorem tailTrace_4909819 : CollatzResearch.WordTrace tailWord_4909819 prefixEnd_4909819 2521097073577431044282659 := by
  unfold tailWord_4909819
  simp only [CollatzResearch.WordTrace]
  refine ⟨179075810599571768171500511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119383873733047845447667007 179075810599571768171500511)
  ·
    refine ⟨268613715899357652257250767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179075810599571768171500511 268613715899357652257250767)
    ·
      refine ⟨402920573849036478385876151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268613715899357652257250767 402920573849036478385876151)
      ·
        refine ⟨604380860773554717578814227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 402920573849036478385876151 604380860773554717578814227)
        ·
          refine ⟨906571291160332076368221341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 604380860773554717578814227 906571291160332076368221341)
          ·
            refine ⟨339964234185124528638083003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 906571291160332076368221341 339964234185124528638083003)
            ·
              refine ⟨509946351277686792957124505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 339964234185124528638083003 509946351277686792957124505)
              ·
                refine ⟨382459763458265094717843379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 509946351277686792957124505 382459763458265094717843379)
                ·
                  refine ⟨573689645187397642076765069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 382459763458265094717843379 573689645187397642076765069)
                  ·
                    refine ⟨215133616945274115778786901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 573689645187397642076765069 215133616945274115778786901)
                    ·
                      refine ⟨2521097073577431044282659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 215133616945274115778786901 2521097073577431044282659)
                      ·
                        rfl

theorem cell23_4909819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 3, 8].length) (baseStart_4909819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909819 prefixEnd_4909819 := by exact prefixLift 4909819
  have htrace : WordTrace (prefixWord ++ tailWord_4909819) baseStart_4909819 baseEnd_4909819 := by
    simpa [prefixWord, tailWord_4909819, baseEnd_4909819] using wordTrace_append hprefix tailTrace_4909819
  have hstable : (prefixWord ++ tailWord_4909819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909819).length < 2 ^ (prefixWord ++ tailWord_4909819).sum := by decide
  have hdescent : baseEnd_4909819 < baseStart_4909819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909878 : List Nat := [5, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2]
def baseStart_4909878 : Nat := 118140960795 + 4909878 * 2 ^ 59
def prefixEnd_4909878 : Nat := 4983230072969 + 3 ^ 40 * 4909878 * 2
def baseEnd_4909878 : Nat := 2521127368936046313444889

theorem tailTrace_4909878 : CollatzResearch.WordTrace tailWord_4909878 prefixEnd_4909878 2521127368936046313444889 := by
  unfold tailWord_4909878
  simp only [CollatzResearch.WordTrace]
  refine ⟨11192372656647376327993643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 119385308337572014165265525 11192372656647376327993643)
  ·
    refine ⟨16788558984971064491990465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11192372656647376327993643 16788558984971064491990465)
    ·
      refine ⟨12591419238728298368992849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 16788558984971064491990465 12591419238728298368992849)
      ·
        refine ⟨9443564429046223776744637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12591419238728298368992849 9443564429046223776744637)
        ·
          refine ⟨3541336660892333916279239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9443564429046223776744637 3541336660892333916279239)
          ·
            refine ⟨5312004991338500874418859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541336660892333916279239 5312004991338500874418859)
            ·
              refine ⟨7968007487007751311628289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312004991338500874418859 7968007487007751311628289)
              ·
                refine ⟨5976005615255813483721217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7968007487007751311628289 5976005615255813483721217)
                ·
                  refine ⟨4482004211441860112790913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5976005615255813483721217 4482004211441860112790913)
                  ·
                    refine ⟨3361503158581395084593185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482004211441860112790913 3361503158581395084593185)
                    ·
                      refine ⟨2521127368936046313444889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361503158581395084593185 2521127368936046313444889)
                      ·
                        rfl

theorem cell23_4909878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 3, 1, 1, 2, 2, 2, 2].length) (baseStart_4909878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909878 prefixEnd_4909878 := by exact prefixLift 4909878
  have htrace : WordTrace (prefixWord ++ tailWord_4909878) baseStart_4909878 baseEnd_4909878 := by
    simpa [prefixWord, tailWord_4909878, baseEnd_4909878] using wordTrace_append hprefix tailTrace_4909878
  have hstable : (prefixWord ++ tailWord_4909878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909878).length < 2 ^ (prefixWord ++ tailWord_4909878).sum := by decide
  have hdescent : baseEnd_4909878 < baseStart_4909878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909896 : List Nat := [2, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6]
def baseStart_4909896 : Nat := 118140960795 + 4909896 * 2 ^ 59
def prefixEnd_4909896 : Nat := 4983230072969 + 3 ^ 40 * 4909896 * 2
def baseEnd_4909896 : Nat := 2521136611587827243019805

theorem tailTrace_4909896 : CollatzResearch.WordTrace tailWord_4909896 prefixEnd_4909896 2521136611587827243019805 := by
  unfold tailWord_4909896
  simp only [CollatzResearch.WordTrace]
  refine ⟨89539309510146405161026771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119385746013528540214702361 89539309510146405161026771)
  ·
    refine ⟨134308964265219607741540157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89539309510146405161026771 134308964265219607741540157)
    ·
      refine ⟨50365861599457352903077559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134308964265219607741540157 50365861599457352903077559)
      ·
        refine ⟨75548792399186029354616339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50365861599457352903077559 75548792399186029354616339)
        ·
          refine ⟨113323188598779044031924509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75548792399186029354616339 113323188598779044031924509)
          ·
            refine ⟨42496195724542141511971691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113323188598779044031924509 42496195724542141511971691)
            ·
              refine ⟨63744293586813212267957537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42496195724542141511971691 63744293586813212267957537)
              ·
                refine ⟨47808220190109909200968153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 63744293586813212267957537 47808220190109909200968153)
                ·
                  refine ⟨35856165142582431900726115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47808220190109909200968153 35856165142582431900726115)
                  ·
                    refine ⟨53784247713873647851089173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 35856165142582431900726115 53784247713873647851089173)
                    ·
                      refine ⟨2521136611587827243019805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53784247713873647851089173 2521136611587827243019805)
                      ·
                        rfl

theorem cell23_4909896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 2, 2, 1, 6].length) (baseStart_4909896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909896 prefixEnd_4909896 := by exact prefixLift 4909896
  have htrace : WordTrace (prefixWord ++ tailWord_4909896) baseStart_4909896 baseEnd_4909896 := by
    simpa [prefixWord, tailWord_4909896, baseEnd_4909896] using wordTrace_append hprefix tailTrace_4909896
  have hstable : (prefixWord ++ tailWord_4909896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909896).length < 2 ^ (prefixWord ++ tailWord_4909896).sum := by decide
  have hdescent : baseEnd_4909896 < baseStart_4909896 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909900 : List Nat := [2, 2, 1, 3, 3, 1, 2, 1, 2, 4, 2]
def baseStart_4909900 : Nat := 118140960795 + 4909900 * 2 ^ 59
def prefixEnd_4909900 : Nat := 4983230072969 + 3 ^ 40 * 4909900 * 2
def baseEnd_4909900 : Nat := 2521138665510445227369787

theorem tailTrace_4909900 : CollatzResearch.WordTrace tailWord_4909900 prefixEnd_4909900 2521138665510445227369787 := by
  unfold tailWord_4909900
  simp only [CollatzResearch.WordTrace]
  refine ⟨89539382456139159502599577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119385843274852212670132769 89539382456139159502599577)
  ·
    refine ⟨67154536842104369626949683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89539382456139159502599577 67154536842104369626949683)
    ·
      refine ⟨100731805263156554440424525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67154536842104369626949683 100731805263156554440424525)
      ·
        refine ⟨37774426973683707915159197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100731805263156554440424525 37774426973683707915159197)
        ·
          refine ⟨14165410115131390468184699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37774426973683707915159197 14165410115131390468184699)
          ·
            refine ⟨21248115172697085702277049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14165410115131390468184699 21248115172697085702277049)
            ·
              refine ⟨15936086379522814276707787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21248115172697085702277049 15936086379522814276707787)
              ·
                refine ⟨23904129569284221415061681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15936086379522814276707787 23904129569284221415061681)
                ·
                  refine ⟨17928097176963166061296261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23904129569284221415061681 17928097176963166061296261)
                  ·
                    refine ⟨3361518220680593636493049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17928097176963166061296261 3361518220680593636493049)
                    ·
                      refine ⟨2521138665510445227369787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361518220680593636493049 2521138665510445227369787)
                      ·
                        rfl

theorem cell23_4909900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 2, 1, 2, 4, 2].length) (baseStart_4909900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909900 prefixEnd_4909900 := by exact prefixLift 4909900
  have htrace : WordTrace (prefixWord ++ tailWord_4909900) baseStart_4909900 baseEnd_4909900 := by
    simpa [prefixWord, tailWord_4909900, baseEnd_4909900] using wordTrace_append hprefix tailTrace_4909900
  have hstable : (prefixWord ++ tailWord_4909900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909900).length < 2 ^ (prefixWord ++ tailWord_4909900).sum := by decide
  have hdescent : baseEnd_4909900 < baseStart_4909900 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909927 : List Nat := [1, 1, 5, 1, 2, 2, 3, 3, 1, 4]
def baseStart_4909927 : Nat := 118140960795 + 4909927 * 2 ^ 59
def prefixEnd_4909927 : Nat := 4983230072969 + 3 ^ 40 * 4909927 * 2
def baseEnd_4909927 : Nat := 840384176496038873910721

theorem tailTrace_4909927 : CollatzResearch.WordTrace tailWord_4909927 prefixEnd_4909927 840384176496038873910721 := by
  unfold tailWord_4909927
  simp only [CollatzResearch.WordTrace]
  refine ⟨179079749683180502616432035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119386499788787001744288023 179079749683180502616432035)
  ·
    refine ⟨268619624524770753924648053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179079749683180502616432035 268619624524770753924648053)
    ·
      refine ⟨25183089799197258180435755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 268619624524770753924648053 25183089799197258180435755)
      ·
        refine ⟨37774634698795887270653633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25183089799197258180435755 37774634698795887270653633)
        ·
          refine ⟨28330976024096915452990225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 37774634698795887270653633 28330976024096915452990225)
          ·
            refine ⟨21248232018072686589742669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28330976024096915452990225 21248232018072686589742669)
            ·
              refine ⟨7968087006777257471153501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21248232018072686589742669 7968087006777257471153501)
              ·
                refine ⟨2988032627541471551682563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7968087006777257471153501 2988032627541471551682563)
                ·
                  refine ⟨4482048941312207327523845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988032627541471551682563 4482048941312207327523845)
                  ·
                    refine ⟨840384176496038873910721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4482048941312207327523845 840384176496038873910721)
                    ·
                      rfl

theorem cell23_4909927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 3, 3, 1, 4].length) (baseStart_4909927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909927 prefixEnd_4909927 := by exact prefixLift 4909927
  have htrace : WordTrace (prefixWord ++ tailWord_4909927) baseStart_4909927 baseEnd_4909927 := by
    simpa [prefixWord, tailWord_4909927, baseEnd_4909927] using wordTrace_append hprefix tailTrace_4909927
  have hstable : (prefixWord ++ tailWord_4909927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909927).length < 2 ^ (prefixWord ++ tailWord_4909927).sum := by decide
  have hdescent : baseEnd_4909927 < baseStart_4909927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909946 : List Nat := [3, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7]
def baseStart_4909946 : Nat := 118140960795 + 4909946 * 2 ^ 59
def prefixEnd_4909946 : Nat := 4983230072969 + 3 ^ 40 * 4909946 * 2
def baseEnd_4909946 : Nat := 2521162285620552047394575

theorem tailTrace_4909946 : CollatzResearch.WordTrace tailWord_4909946 prefixEnd_4909946 2521162285620552047394575 := by
  unfold tailWord_4909946
  simp only [CollatzResearch.WordTrace]
  refine ⟨44770110667527917215343423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119386961780074445907582461 44770110667527917215343423)
  ·
    refine ⟨67155166001291875823015135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44770110667527917215343423 67155166001291875823015135)
    ·
      refine ⟨100732749001937813734522703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67155166001291875823015135 100732749001937813734522703)
      ·
        refine ⟨151099123502906720601784055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100732749001937813734522703 151099123502906720601784055)
        ·
          refine ⟨226648685254360080902676083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151099123502906720601784055 226648685254360080902676083)
          ·
            refine ⟨339973027881540121354014125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226648685254360080902676083 339973027881540121354014125)
            ·
              refine ⟨127489885455577545507755297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 339973027881540121354014125 127489885455577545507755297)
              ·
                refine ⟨95617414091683159130816473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127489885455577545507755297 95617414091683159130816473)
                ·
                  refine ⟨71713060568762369348112355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 95617414091683159130816473 71713060568762369348112355)
                  ·
                    refine ⟨107569590853143554022168533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71713060568762369348112355 107569590853143554022168533)
                    ·
                      refine ⟨2521162285620552047394575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107569590853143554022168533 2521162285620552047394575)
                      ·
                        rfl

theorem cell23_4909946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 3, 2, 2, 1, 7].length) (baseStart_4909946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909946 prefixEnd_4909946 := by exact prefixLift 4909946
  have htrace : WordTrace (prefixWord ++ tailWord_4909946) baseStart_4909946 baseEnd_4909946 := by
    simpa [prefixWord, tailWord_4909946, baseEnd_4909946] using wordTrace_append hprefix tailTrace_4909946
  have hstable : (prefixWord ++ tailWord_4909946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909946).length < 2 ^ (prefixWord ++ tailWord_4909946).sum := by decide
  have hdescent : baseEnd_4909946 < baseStart_4909946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4909983 : List Nat := [1, 1, 2, 5, 2, 1, 1, 1, 3, 6]
def baseStart_4909983 : Nat := 118140960795 + 4909983 * 2 ^ 59
def prefixEnd_4909983 : Nat := 4983230072969 + 3 ^ 40 * 4909983 * 2
def baseEnd_4909983 : Nat := 840393761468256134210635

theorem tailTrace_4909983 : CollatzResearch.WordTrace tailWord_4909983 prefixEnd_4909983 840393761468256134210635 := by
  unfold tailWord_4909983
  simp only [CollatzResearch.WordTrace]
  refine ⟨179081792170977624180470603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119387861447318416120313735 179081792170977624180470603)
  ·
    refine ⟨268622688256466436270705905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179081792170977624180470603 268622688256466436270705905)
    ·
      refine ⟨201467016192349827203029429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268622688256466436270705905 201467016192349827203029429)
      ·
        refine ⟨18887532768032796300284009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 201467016192349827203029429 18887532768032796300284009)
        ·
          refine ⟨14165649576024597225213007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18887532768032796300284009 14165649576024597225213007)
          ·
            refine ⟨21248474364036895837819511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14165649576024597225213007 21248474364036895837819511)
            ·
              refine ⟨31872711546055343756729267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21248474364036895837819511 31872711546055343756729267)
              ·
                refine ⟨47809067319083015635093901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31872711546055343756729267 47809067319083015635093901)
                ·
                  refine ⟨17928400244656130863160213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47809067319083015635093901 17928400244656130863160213)
                  ·
                    refine ⟨840393761468256134210635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17928400244656130863160213 840393761468256134210635)
                    ·
                      rfl

theorem cell23_4909983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 1, 1, 3, 6].length) (baseStart_4909983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4909983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4909983 prefixEnd_4909983 := by exact prefixLift 4909983
  have htrace : WordTrace (prefixWord ++ tailWord_4909983) baseStart_4909983 baseEnd_4909983 := by
    simpa [prefixWord, tailWord_4909983, baseEnd_4909983] using wordTrace_append hprefix tailTrace_4909983
  have hstable : (prefixWord ++ tailWord_4909983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4909983).length < 2 ^ (prefixWord ++ tailWord_4909983).sum := by decide
  have hdescent : baseEnd_4909983 < baseStart_4909983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4909983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910024 : List Nat := [2, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2]
def baseStart_4910024 : Nat := 118140960795 + 4910024 * 2 ^ 59
def prefixEnd_4910024 : Nat := 4983230072969 + 3 ^ 40 * 4910024 * 2
def baseEnd_4910024 : Nat := 2521202337111602742219217

theorem tailTrace_4910024 : CollatzResearch.WordTrace tailWord_4910024 prefixEnd_4910024 2521202337111602742219217 := by
  unfold tailWord_4910024
  simp only [CollatzResearch.WordTrace]
  refine ⟨89541643781914544091356563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119388858375886058788475417 89541643781914544091356563)
  ·
    refine ⟨134312465672871816137034845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89541643781914544091356563 134312465672871816137034845)
    ·
      refine ⟨50367174627326931051388067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134312465672871816137034845 50367174627326931051388067)
      ·
        refine ⟨75550761940990396577082101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50367174627326931051388067 75550761940990396577082101)
        ·
          refine ⟨7082883931967849679101447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 75550761940990396577082101 7082883931967849679101447)
          ·
            refine ⟨10624325897951774518652171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7082883931967849679101447 10624325897951774518652171)
            ·
              refine ⟨15936488846927661777978257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10624325897951774518652171 15936488846927661777978257)
              ·
                refine ⟨11952366635195746333483693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15936488846927661777978257 11952366635195746333483693)
                ·
                  refine ⟨4482137488198404875056385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11952366635195746333483693 4482137488198404875056385)
                  ·
                    refine ⟨3361603116148803656292289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482137488198404875056385 3361603116148803656292289)
                    ·
                      refine ⟨2521202337111602742219217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361603116148803656292289 2521202337111602742219217)
                      ·
                        rfl

theorem cell23_4910024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 1, 2, 3, 2, 2].length) (baseStart_4910024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910024 prefixEnd_4910024 := by exact prefixLift 4910024
  have htrace : WordTrace (prefixWord ++ tailWord_4910024) baseStart_4910024 baseEnd_4910024 := by
    simpa [prefixWord, tailWord_4910024, baseEnd_4910024] using wordTrace_append hprefix tailTrace_4910024
  have hstable : (prefixWord ++ tailWord_4910024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910024).length < 2 ^ (prefixWord ++ tailWord_4910024).sum := by decide
  have hdescent : baseEnd_4910024 < baseStart_4910024 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910030 : List Nat := [4, 1, 1, 1, 2, 4, 3, 7]
def baseStart_4910030 : Nat := 118140960795 + 4910030 * 2 ^ 59
def prefixEnd_4910030 : Nat := 4983230072969 + 3 ^ 40 * 4910030 * 2
def baseEnd_4910030 : Nat := 93377978444278878472007

theorem tailTrace_4910030 : CollatzResearch.WordTrace tailWord_4910030 prefixEnd_4910030 93377978444278878472007 := by
  unfold tailWord_4910030
  simp only [CollatzResearch.WordTrace]
  refine ⟨22385438300225918900928943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 119389004267871567471621029 22385438300225918900928943)
  ·
    refine ⟨33578157450338878351393415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22385438300225918900928943 33578157450338878351393415)
    ·
      refine ⟨50367236175508317527090123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33578157450338878351393415 50367236175508317527090123)
      ·
        refine ⟨75550854263262476290635185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50367236175508317527090123 75550854263262476290635185)
        ·
          refine ⟨56663140697446857217976389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75550854263262476290635185 56663140697446857217976389)
          ·
            refine ⟨10624338880771285728370573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56663140697446857217976389 10624338880771285728370573)
            ·
              refine ⟨3984127080289232148138965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10624338880771285728370573 3984127080289232148138965)
              ·
                refine ⟨93377978444278878472007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3984127080289232148138965 93377978444278878472007)
                ·
                  rfl

theorem cell23_4910030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 3, 7].length) (baseStart_4910030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910030 prefixEnd_4910030 := by exact prefixLift 4910030
  have htrace : WordTrace (prefixWord ++ tailWord_4910030) baseStart_4910030 baseEnd_4910030 := by
    simpa [prefixWord, tailWord_4910030, baseEnd_4910030] using wordTrace_append hprefix tailTrace_4910030
  have hstable : (prefixWord ++ tailWord_4910030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910030).length < 2 ^ (prefixWord ++ tailWord_4910030).sum := by decide
  have hdescent : baseEnd_4910030 < baseStart_4910030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910040 : List Nat := [2, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3]
def baseStart_4910040 : Nat := 118140960795 + 4910040 * 2 ^ 59
def prefixEnd_4910040 : Nat := 4983230072969 + 3 ^ 40 * 4910040 * 2
def baseEnd_4910040 : Nat := 2521210552802074679619143

theorem tailTrace_4910040 : CollatzResearch.WordTrace tailWord_4910040 prefixEnd_4910040 2521210552802074679619143 := by
  unfold tailWord_4910040
  simp only [CollatzResearch.WordTrace]
  refine ⟨89541935565885561457647787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119389247421180748610197049 89541935565885561457647787)
  ·
    refine ⟨134312903348828342186471681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89541935565885561457647787 134312903348828342186471681)
    ·
      refine ⟨100734677511621256639853761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134312903348828342186471681 100734677511621256639853761)
      ·
        refine ⟨75551008133715942479890321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100734677511621256639853761 75551008133715942479890321)
        ·
          refine ⟨56663256100286956859917741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75551008133715942479890321 56663256100286956859917741)
          ·
            refine ⟨21248721037607608822469153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56663256100286956859917741 21248721037607608822469153)
            ·
              refine ⟨15936540778205706616851865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21248721037607608822469153 15936540778205706616851865)
              ·
                refine ⟨11952405583654279962638899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 15936540778205706616851865 11952405583654279962638899)
                ·
                  refine ⟨17928608375481419943958349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11952405583654279962638899 17928608375481419943958349)
                  ·
                    refine ⟨6723228140805532478984381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17928608375481419943958349 6723228140805532478984381)
                    ·
                      refine ⟨2521210552802074679619143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723228140805532478984381 2521210552802074679619143)
                      ·
                        rfl

theorem cell23_4910040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_4910040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910040 prefixEnd_4910040 := by exact prefixLift 4910040
  have htrace : WordTrace (prefixWord ++ tailWord_4910040) baseStart_4910040 baseEnd_4910040 := by
    simpa [prefixWord, tailWord_4910040, baseEnd_4910040] using wordTrace_append hprefix tailTrace_4910040
  have hstable : (prefixWord ++ tailWord_4910040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910040).length < 2 ^ (prefixWord ++ tailWord_4910040).sum := by decide
  have hdescent : baseEnd_4910040 < baseStart_4910040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910041 : List Nat := [1, 2, 1, 2, 5, 2, 2, 3, 1, 2, 2]
def baseStart_4910041 : Nat := 118140960795 + 4910041 * 2 ^ 59
def prefixEnd_4910041 : Nat := 4983230072969 + 3 ^ 40 * 4910041 * 2
def baseEnd_4910041 : Nat := 2521211066282729175706639

theorem tailTrace_4910041 : CollatzResearch.WordTrace tailWord_4910041 prefixEnd_4910041 2521211066282729175706639 := by
  unfold tailWord_4910041
  simp only [CollatzResearch.WordTrace]
  refine ⟨179083907604767500086081977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119389271736511666724054651 179083907604767500086081977)
  ·
    refine ⟨134312930703575625064561483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179083907604767500086081977 134312930703575625064561483)
    ·
      refine ⟨201469396055363437596842225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134312930703575625064561483 201469396055363437596842225)
      ·
        refine ⟨151102047041522578197631669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201469396055363437596842225 151102047041522578197631669)
        ·
          refine ⟨14165816910142741706027969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 151102047041522578197631669 14165816910142741706027969)
          ·
            refine ⟨10624362682607056279520977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14165816910142741706027969 10624362682607056279520977)
            ·
              refine ⟨7968272011955292209640733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10624362682607056279520977 7968272011955292209640733)
              ·
                refine ⟨2988102004483234578615275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7968272011955292209640733 2988102004483234578615275)
                ·
                  refine ⟨4482153006724851867922913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988102004483234578615275 4482153006724851867922913)
                  ·
                    refine ⟨3361614755043638900942185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482153006724851867922913 3361614755043638900942185)
                    ·
                      refine ⟨2521211066282729175706639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361614755043638900942185 2521211066282729175706639)
                      ·
                        rfl

theorem cell23_4910041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 2, 3, 1, 2, 2].length) (baseStart_4910041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910041 prefixEnd_4910041 := by exact prefixLift 4910041
  have htrace : WordTrace (prefixWord ++ tailWord_4910041) baseStart_4910041 baseEnd_4910041 := by
    simpa [prefixWord, tailWord_4910041, baseEnd_4910041] using wordTrace_append hprefix tailTrace_4910041
  have hstable : (prefixWord ++ tailWord_4910041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910041).length < 2 ^ (prefixWord ++ tailWord_4910041).sum := by decide
  have hdescent : baseEnd_4910041 < baseStart_4910041 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910068 : List Nat := [2, 6, 2, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4910068 : Nat := 118140960795 + 4910068 * 2 ^ 59
def prefixEnd_4910068 : Nat := 4983230072969 + 3 ^ 40 * 4910068 * 2
def baseEnd_4910068 : Nat := 840408310086800190023005

theorem tailTrace_4910068 : CollatzResearch.WordTrace tailWord_4910068 prefixEnd_4910068 840408310086800190023005 := by
  unfold tailWord_4910068
  simp only [CollatzResearch.WordTrace]
  refine ⟨89542446187834841848657429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119389928250446455798209905 89542446187834841848657429)
  ·
    refine ⟨4197302165054758211655817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 89542446187834841848657429 4197302165054758211655817)
    ·
      refine ⟨3147976623791068658741863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4197302165054758211655817 3147976623791068658741863)
      ·
        refine ⟨4721964935686602988112795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3147976623791068658741863 4721964935686602988112795)
        ·
          refine ⟨7082947403529904482169193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4721964935686602988112795 7082947403529904482169193)
          ·
            refine ⟨5312210552647428361626895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7082947403529904482169193 5312210552647428361626895)
            ·
              refine ⟨7968315828971142542440343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312210552647428361626895 7968315828971142542440343)
              ·
                refine ⟨11952473743456713813660515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7968315828971142542440343 11952473743456713813660515)
                ·
                  refine ⟨17928710615185070720490773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11952473743456713813660515 17928710615185070720490773)
                  ·
                    refine ⟨840408310086800190023005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17928710615185070720490773 840408310086800190023005)
                    ·
                      rfl

theorem cell23_4910068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4910068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910068 prefixEnd_4910068 := by exact prefixLift 4910068
  have htrace : WordTrace (prefixWord ++ tailWord_4910068) baseStart_4910068 baseEnd_4910068 := by
    simpa [prefixWord, tailWord_4910068, baseEnd_4910068] using wordTrace_append hprefix tailTrace_4910068
  have hstable : (prefixWord ++ tailWord_4910068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910068).length < 2 ^ (prefixWord ++ tailWord_4910068).sum := by decide
  have hdescent : baseEnd_4910068 < baseStart_4910068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910073 : List Nat := [1, 2, 1, 3, 1, 3, 1, 3, 2, 6]
def baseStart_4910073 : Nat := 118140960795 + 4910073 * 2 ^ 59
def prefixEnd_4910073 : Nat := 4983230072969 + 3 ^ 40 * 4910073 * 2
def baseEnd_4910073 : Nat := 840409165887891016835497

theorem tailTrace_4910073 : CollatzResearch.WordTrace tailWord_4910073 prefixEnd_4910073 840409165887891016835497 := by
  unfold tailWord_4910073
  simp only [CollatzResearch.WordTrace]
  refine ⟨179085074740651569551246873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119390049827101046367497915 179085074740651569551246873)
  ·
    refine ⟨134313806055488677163435155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179085074740651569551246873 134313806055488677163435155)
    ·
      refine ⟨201470709083233015745152733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134313806055488677163435155 201470709083233015745152733)
      ·
        refine ⟨75551515906212380904432275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201470709083233015745152733 75551515906212380904432275)
        ·
          refine ⟨113327273859318571356648413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75551515906212380904432275 113327273859318571356648413)
          ·
            refine ⟨42497727697244464258743155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 113327273859318571356648413 42497727697244464258743155)
            ·
              refine ⟨63746591545866696388114733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42497727697244464258743155 63746591545866696388114733)
              ·
                refine ⟨23904971829700011145543025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63746591545866696388114733 23904971829700011145543025)
                ·
                  refine ⟨17928728872275008359157269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 23904971829700011145543025 17928728872275008359157269)
                  ·
                    refine ⟨840409165887891016835497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17928728872275008359157269 840409165887891016835497)
                    ·
                      rfl

theorem cell23_4910073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 3, 2, 6].length) (baseStart_4910073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910073 prefixEnd_4910073 := by exact prefixLift 4910073
  have htrace : WordTrace (prefixWord ++ tailWord_4910073) baseStart_4910073 baseEnd_4910073 := by
    simpa [prefixWord, tailWord_4910073, baseEnd_4910073] using wordTrace_append hprefix tailTrace_4910073
  have hstable : (prefixWord ++ tailWord_4910073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910073).length < 2 ^ (prefixWord ++ tailWord_4910073).sum := by decide
  have hdescent : baseEnd_4910073 < baseStart_4910073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910114 : List Nat := [3, 3, 1, 1, 1, 3, 2, 1, 4, 2, 2]
def baseStart_4910114 : Nat := 118140960795 + 4910114 * 2 ^ 59
def prefixEnd_4910114 : Nat := 4983230072969 + 3 ^ 40 * 4910114 * 2
def baseEnd_4910114 : Nat := 2521248550370507390093803

theorem tailTrace_4910114 : CollatzResearch.WordTrace tailWord_4910114 prefixEnd_4910114 2521248550370507390093803 := by
  unfold tailWord_4910114
  simp only [CollatzResearch.WordTrace]
  refine ⟨44771642533375758388372349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119391046755668689035659597 44771642533375758388372349)
  ·
    refine ⟨16789365950015909395639631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 44771642533375758388372349 16789365950015909395639631)
    ·
      refine ⟨25184048925023864093459447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16789365950015909395639631 25184048925023864093459447)
      ·
        refine ⟨37776073387535796140189171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25184048925023864093459447 37776073387535796140189171)
        ·
          refine ⟨56664110081303694210283757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37776073387535796140189171 56664110081303694210283757)
          ·
            refine ⟨21249041280488885328856409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56664110081303694210283757 21249041280488885328856409)
            ·
              refine ⟨15936780960366663996642307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21249041280488885328856409 15936780960366663996642307)
              ·
                refine ⟨23905171440549995994963461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15936780960366663996642307 23905171440549995994963461)
                ·
                  refine ⟨4482219645103124249055649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 23905171440549995994963461 4482219645103124249055649)
                  ·
                    refine ⟨3361664733827343186791737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4482219645103124249055649 3361664733827343186791737)
                    ·
                      refine ⟨2521248550370507390093803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361664733827343186791737 2521248550370507390093803)
                      ·
                        rfl

theorem cell23_4910114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 2, 1, 4, 2, 2].length) (baseStart_4910114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910114 prefixEnd_4910114 := by exact prefixLift 4910114
  have htrace : WordTrace (prefixWord ++ tailWord_4910114) baseStart_4910114 baseEnd_4910114 := by
    simpa [prefixWord, tailWord_4910114, baseEnd_4910114] using wordTrace_append hprefix tailTrace_4910114
  have hstable : (prefixWord ++ tailWord_4910114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910114).length < 2 ^ (prefixWord ++ tailWord_4910114).sum := by decide
  have hdescent : baseEnd_4910114 < baseStart_4910114 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910130 : List Nat := [3, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_4910130 : Nat := 118140960795 + 4910130 * 2 ^ 59
def prefixEnd_4910130 : Nat := 4983230072969 + 3 ^ 40 * 4910130 * 2
def baseEnd_4910130 : Nat := 2521256766060979327493729

theorem tailTrace_4910130 : CollatzResearch.WordTrace tailWord_4910130 prefixEnd_4910130 2521256766060979327493729 := by
  unfold tailWord_4910130
  simp only [CollatzResearch.WordTrace]
  refine ⟨44771788425361267071517961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119391435800963378857381229 44771788425361267071517961)
  ·
    refine ⟨33578841319020950303638471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 44771788425361267071517961 33578841319020950303638471)
    ·
      refine ⟨50368261978531425455457707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33578841319020950303638471 50368261978531425455457707)
      ·
        refine ⟨75552392967797138183186561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50368261978531425455457707 75552392967797138183186561)
        ·
          refine ⟨56664294725847853637389921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75552392967797138183186561 56664294725847853637389921)
          ·
            refine ⟨42498221044385890228042441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56664294725847853637389921 42498221044385890228042441)
            ·
              refine ⟨31873665783289417671031831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 42498221044385890228042441 31873665783289417671031831)
              ·
                refine ⟨47810498674934126506547747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31873665783289417671031831 47810498674934126506547747)
                ·
                  refine ⟨71715748012401189759821621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 47810498674934126506547747 71715748012401189759821621)
                  ·
                    refine ⟨6723351376162611539983277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 71715748012401189759821621 6723351376162611539983277)
                    ·
                      refine ⟨2521256766060979327493729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723351376162611539983277 2521256766060979327493729)
                      ·
                        rfl

theorem cell23_4910130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_4910130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910130 prefixEnd_4910130 := by exact prefixLift 4910130
  have htrace : WordTrace (prefixWord ++ tailWord_4910130) baseStart_4910130 baseEnd_4910130 := by
    simpa [prefixWord, tailWord_4910130, baseEnd_4910130] using wordTrace_append hprefix tailTrace_4910130
  have hstable : (prefixWord ++ tailWord_4910130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910130).length < 2 ^ (prefixWord ++ tailWord_4910130).sum := by decide
  have hdescent : baseEnd_4910130 < baseStart_4910130 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910143 : List Nat := [1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7]
def baseStart_4910143 : Nat := 118140960795 + 4910143 * 2 ^ 59
def prefixEnd_4910143 : Nat := 4983230072969 + 3 ^ 40 * 4910143 * 2
def baseEnd_4910143 : Nat := 2521263441309487776631169

theorem tailTrace_4910143 : CollatzResearch.WordTrace tailWord_4910143 prefixEnd_4910143 2521263441309487776631169 := by
  unfold tailWord_4910143
  simp only [CollatzResearch.WordTrace]
  refine ⟨179087627850397971506295083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119391751900265314337530055 179087627850397971506295083)
  ·
    refine ⟨268631441775596957259442625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179087627850397971506295083 268631441775596957259442625)
    ·
      refine ⟨201473581331697717944581969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268631441775596957259442625 201473581331697717944581969)
      ·
        refine ⟨151105185998773288458436477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201473581331697717944581969 151105185998773288458436477)
        ·
          refine ⟨56664444749539983171913679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151105185998773288458436477 56664444749539983171913679)
          ·
            refine ⟨84996667124309974757870519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56664444749539983171913679 84996667124309974757870519)
            ·
              refine ⟨127495000686464962136805779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84996667124309974757870519 127495000686464962136805779)
              ·
                refine ⟨191242501029697443205208669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127495000686464962136805779 191242501029697443205208669)
                ·
                  refine ⟨71715937886136541201953251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 191242501029697443205208669 71715937886136541201953251)
                  ·
                    refine ⟨107573906829204811802929877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 71715937886136541201953251 107573906829204811802929877)
                    ·
                      refine ⟨2521263441309487776631169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107573906829204811802929877 2521263441309487776631169)
                      ·
                        rfl

theorem cell23_4910143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_4910143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910143 prefixEnd_4910143 := by exact prefixLift 4910143
  have htrace : WordTrace (prefixWord ++ tailWord_4910143) baseStart_4910143 baseEnd_4910143 := by
    simpa [prefixWord, tailWord_4910143, baseEnd_4910143] using wordTrace_append hprefix tailTrace_4910143
  have hstable : (prefixWord ++ tailWord_4910143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910143).length < 2 ^ (prefixWord ++ tailWord_4910143).sum := by decide
  have hdescent : baseEnd_4910143 < baseStart_4910143 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910170 : List Nat := [3, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4]
def baseStart_4910170 : Nat := 118140960795 + 4910170 * 2 ^ 59
def prefixEnd_4910170 : Nat := 4983230072969 + 3 ^ 40 * 4910170 * 2
def baseEnd_4910170 : Nat := 2521277305287159170993545

theorem tailTrace_4910170 : CollatzResearch.WordTrace tailWord_4910170 prefixEnd_4910170 2521277305287159170993545 := by
  unfold tailWord_4910170
  simp only [CollatzResearch.WordTrace]
  refine ⟨44772153155325038779381991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119392408414200103411685309 44772153155325038779381991)
  ·
    refine ⟨67158229732987558169072987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44772153155325038779381991 67158229732987558169072987)
    ·
      refine ⟨100737344599481337253609481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67158229732987558169072987 100737344599481337253609481)
      ·
        refine ⟨75553008449611002940207111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100737344599481337253609481 75553008449611002940207111)
        ·
          refine ⟨113329512674416504410310667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75553008449611002940207111 113329512674416504410310667)
          ·
            refine ⟨169994269011624756615466001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113329512674416504410310667 169994269011624756615466001)
            ·
              refine ⟨127495701758718567461599501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 169994269011624756615466001 127495701758718567461599501)
              ·
                refine ⟨47810888159519462798099813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 127495701758718567461599501 47810888159519462798099813)
                ·
                  refine ⟨8964541529909899274643715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 47810888159519462798099813 8964541529909899274643715)
                  ·
                    refine ⟨13446812294864848911965573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8964541529909899274643715 13446812294864848911965573)
                    ·
                      refine ⟨2521277305287159170993545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13446812294864848911965573 2521277305287159170993545)
                      ·
                        rfl

theorem cell23_4910170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4].length) (baseStart_4910170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910170 prefixEnd_4910170 := by exact prefixLift 4910170
  have htrace : WordTrace (prefixWord ++ tailWord_4910170) baseStart_4910170 baseEnd_4910170 := by
    simpa [prefixWord, tailWord_4910170, baseEnd_4910170] using wordTrace_append hprefix tailTrace_4910170
  have hstable : (prefixWord ++ tailWord_4910170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910170).length < 2 ^ (prefixWord ++ tailWord_4910170).sum := by decide
  have hdescent : baseEnd_4910170 < baseStart_4910170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910220 : List Nat := [2, 2, 1, 2, 1, 1, 1, 2, 1, 7, 3]
def baseStart_4910220 : Nat := 118140960795 + 4910220 * 2 ^ 59
def prefixEnd_4910220 : Nat := 4983230072969 + 3 ^ 40 * 4910220 * 2
def baseEnd_4910220 : Nat := 2521302979319883975368315

theorem tailTrace_4910220 : CollatzResearch.WordTrace tailWord_4910220 prefixEnd_4910220 2521302979319883975368315 := by
  unfold tailWord_4910220
  simp only [CollatzResearch.WordTrace]
  refine ⟨89545218135559506828424057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119393624180746009104565409 89545218135559506828424057)
  ·
    refine ⟨67158913601669630121318043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89545218135559506828424057 67158913601669630121318043)
    ·
      refine ⟨100738370402504445181977065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67158913601669630121318043 100738370402504445181977065)
      ·
        refine ⟨75553777801878333886482799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 100738370402504445181977065 75553777801878333886482799)
        ·
          refine ⟨113330666702817500829724199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75553777801878333886482799 113330666702817500829724199)
          ·
            refine ⟨169996000054226251244586299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113330666702817500829724199 169996000054226251244586299)
            ·
              refine ⟨254994000081339376866879449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 169996000054226251244586299 254994000081339376866879449)
              ·
                refine ⟨191245500061004532650159587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 254994000081339376866879449 191245500061004532650159587)
                ·
                  refine ⟨286868250091506798975239381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191245500061004532650159587 286868250091506798975239381)
                  ·
                    refine ⟨6723474611519690600982173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 286868250091506798975239381 6723474611519690600982173)
                    ·
                      refine ⟨2521302979319883975368315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723474611519690600982173 2521302979319883975368315)
                      ·
                        rfl

theorem cell23_4910220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_4910220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910220 prefixEnd_4910220 := by exact prefixLift 4910220
  have htrace : WordTrace (prefixWord ++ tailWord_4910220) baseStart_4910220 baseEnd_4910220 := by
    simpa [prefixWord, tailWord_4910220, baseEnd_4910220] using wordTrace_append hprefix tailTrace_4910220
  have hstable : (prefixWord ++ tailWord_4910220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910220).length < 2 ^ (prefixWord ++ tailWord_4910220).sum := by decide
  have hdescent : baseEnd_4910220 < baseStart_4910220 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910244 : List Nat := [2, 3, 1, 2, 3, 2, 3, 1, 6]
def baseStart_4910244 : Nat := 118140960795 + 4910244 * 2 ^ 59
def prefixEnd_4910244 : Nat := 4983230072969 + 3 ^ 40 * 4910244 * 2
def baseEnd_4910244 : Nat := 280146144761732431274245

theorem tailTrace_4910244 : CollatzResearch.WordTrace tailWord_4910244 prefixEnd_4910244 280146144761732431274245 := by
  unfold tailWord_4910244
  simp only [CollatzResearch.WordTrace]
  refine ⟨89545655811516032877860893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119394207748688043837147857 89545655811516032877860893)
  ·
    refine ⟨33579620929318512329197835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 89545655811516032877860893 33579620929318512329197835)
    ·
      refine ⟨50369431393977768493796753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 33579620929318512329197835 50369431393977768493796753)
      ·
        refine ⟨37777073545483326370347565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50369431393977768493796753 37777073545483326370347565)
        ·
          refine ⟨14166402579556247388880337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 37777073545483326370347565 14166402579556247388880337)
          ·
            refine ⟨10624801934667185541660253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14166402579556247388880337 10624801934667185541660253)
            ·
              refine ⟨3984300725500194578122595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10624801934667185541660253 3984300725500194578122595)
              ·
                refine ⟨5976451088250291867183893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3984300725500194578122595 5976451088250291867183893)
                ·
                  refine ⟨280146144761732431274245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5976451088250291867183893 280146144761732431274245)
                  ·
                    rfl

theorem cell23_4910244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 3, 1, 6].length) (baseStart_4910244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910244 prefixEnd_4910244 := by exact prefixLift 4910244
  have htrace : WordTrace (prefixWord ++ tailWord_4910244) baseStart_4910244 baseEnd_4910244 := by
    simpa [prefixWord, tailWord_4910244, baseEnd_4910244] using wordTrace_append hprefix tailTrace_4910244
  have hstable : (prefixWord ++ tailWord_4910244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910244).length < 2 ^ (prefixWord ++ tailWord_4910244).sum := by decide
  have hdescent : baseEnd_4910244 < baseStart_4910244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910271 : List Nat := [1, 1, 2, 2, 2, 2, 5, 3, 1, 1, 3]
def baseStart_4910271 : Nat := 118140960795 + 4910271 * 2 ^ 59
def prefixEnd_4910271 : Nat := 4983230072969 + 3 ^ 40 * 4910271 * 2
def baseEnd_4910271 : Nat := 2521329166833263275830581

theorem tailTrace_4910271 : CollatzResearch.WordTrace tailWord_4910271 prefixEnd_4910271 2521329166833263275830581 := by
  unfold tailWord_4910271
  simp only [CollatzResearch.WordTrace]
  refine ⟨179092296393934249366954667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119394864262622832911303111 179092296393934249366954667)
  ·
    refine ⟨268638444590901374050432001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179092296393934249366954667 268638444590901374050432001)
    ·
      refine ⟨201478833443176030537824001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268638444590901374050432001 201478833443176030537824001)
      ·
        refine ⟨151109125082382022903368001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201478833443176030537824001 151109125082382022903368001)
        ·
          refine ⟨113331843811786517177526001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 151109125082382022903368001 113331843811786517177526001)
          ·
            refine ⟨84998882858839887883144501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 113331843811786517177526001 84998882858839887883144501)
            ·
              refine ⟨7968645268016239489044797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 84998882858839887883144501 7968645268016239489044797)
              ·
                refine ⟨2988241975506089808391799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7968645268016239489044797 2988241975506089808391799)
                ·
                  refine ⟨4482362963259134712587699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2988241975506089808391799 4482362963259134712587699)
                  ·
                    refine ⟨6723544444888702068881549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4482362963259134712587699 6723544444888702068881549)
                    ·
                      refine ⟨2521329166833263275830581, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723544444888702068881549 2521329166833263275830581)
                      ·
                        rfl

theorem cell23_4910271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 5, 3, 1, 1, 3].length) (baseStart_4910271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910271 prefixEnd_4910271 := by exact prefixLift 4910271
  have htrace : WordTrace (prefixWord ++ tailWord_4910271) baseStart_4910271 baseEnd_4910271 := by
    simpa [prefixWord, tailWord_4910271, baseEnd_4910271] using wordTrace_append hprefix tailTrace_4910271
  have hstable : (prefixWord ++ tailWord_4910271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910271).length < 2 ^ (prefixWord ++ tailWord_4910271).sum := by decide
  have hdescent : baseEnd_4910271 < baseStart_4910271 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910297 : List Nat := [1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 3]
def baseStart_4910297 : Nat := 118140960795 + 4910297 * 2 ^ 59
def prefixEnd_4910297 : Nat := 4983230072969 + 3 ^ 40 * 4910297 * 2
def baseEnd_4910297 : Nat := 2521342517330280174105461

theorem tailTrace_4910297 : CollatzResearch.WordTrace tailWord_4910297 prefixEnd_4910297 2521342517330280174105461 := by
  unfold tailWord_4910297
  simp only [CollatzResearch.WordTrace]
  refine ⟨179093244691840055807401145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119395496461226703871600763 179093244691840055807401145)
  ·
    refine ⟨134319933518880041855550859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179093244691840055807401145 134319933518880041855550859)
    ·
      refine ⟨201479900278320062783326289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134319933518880041855550859 201479900278320062783326289)
      ·
        refine ⟨151109925208740047087494717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 201479900278320062783326289 151109925208740047087494717)
        ·
          refine ⟨56666221953277517657810519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 151109925208740047087494717 56666221953277517657810519)
          ·
            refine ⟨84999332929916276486715779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56666221953277517657810519 84999332929916276486715779)
            ·
              refine ⟨127498999394874414730073669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 84999332929916276486715779 127498999394874414730073669)
              ·
                refine ⟨23906062386538952761888813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 127498999394874414730073669 23906062386538952761888813)
                ·
                  refine ⟨8964773394952107285708305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23906062386538952761888813 8964773394952107285708305)
                  ·
                    refine ⟨6723580046214080464281229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8964773394952107285708305 6723580046214080464281229)
                    ·
                      refine ⟨2521342517330280174105461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723580046214080464281229 2521342517330280174105461)
                      ·
                        rfl

theorem cell23_4910297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 1, 4, 3, 2, 3].length) (baseStart_4910297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910297 prefixEnd_4910297 := by exact prefixLift 4910297
  have htrace : WordTrace (prefixWord ++ tailWord_4910297) baseStart_4910297 baseEnd_4910297 := by
    simpa [prefixWord, tailWord_4910297, baseEnd_4910297] using wordTrace_append hprefix tailTrace_4910297
  have hstable : (prefixWord ++ tailWord_4910297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910297).length < 2 ^ (prefixWord ++ tailWord_4910297).sum := by decide
  have hdescent : baseEnd_4910297 < baseStart_4910297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910304 : List Nat := [2, 1, 1, 3, 1, 5, 1, 3, 2, 4]
def baseStart_4910304 : Nat := 118140960795 + 4910304 * 2 ^ 59
def prefixEnd_4910304 : Nat := 4983230072969 + 3 ^ 40 * 4910304 * 2
def baseEnd_4910304 : Nat := 840448703898287215572643

theorem tailTrace_4910304 : CollatzResearch.WordTrace tailWord_4910304 prefixEnd_4910304 840448703898287215572643 := by
  unfold tailWord_4910304
  simp only [CollatzResearch.WordTrace]
  refine ⟨89546750001407348001452983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119395666668543130668603977 89546750001407348001452983)
  ·
    refine ⟨134320125002111022002179475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89546750001407348001452983 134320125002111022002179475)
    ·
      refine ⟨201480187503166533003269213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134320125002111022002179475 201480187503166533003269213)
      ·
        refine ⟨75555070313687449876225955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 201480187503166533003269213 75555070313687449876225955)
        ·
          refine ⟨113332605470531174814338933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75555070313687449876225955 113332605470531174814338933)
          ·
            refine ⟨10624931762862297638844275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 113332605470531174814338933 10624931762862297638844275)
            ·
              refine ⟨15937397644293446458266413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10624931762862297638844275 15937397644293446458266413)
              ·
                refine ⟨5976524116610042421849905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15937397644293446458266413 5976524116610042421849905)
                ·
                  refine ⟨4482393087457531816387429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5976524116610042421849905 4482393087457531816387429)
                  ·
                    refine ⟨840448703898287215572643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4482393087457531816387429 840448703898287215572643)
                    ·
                      rfl

theorem cell23_4910304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 5, 1, 3, 2, 4].length) (baseStart_4910304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910304 prefixEnd_4910304 := by exact prefixLift 4910304
  have htrace : WordTrace (prefixWord ++ tailWord_4910304) baseStart_4910304 baseEnd_4910304 := by
    simpa [prefixWord, tailWord_4910304, baseEnd_4910304] using wordTrace_append hprefix tailTrace_4910304
  have hstable : (prefixWord ++ tailWord_4910304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910304).length < 2 ^ (prefixWord ++ tailWord_4910304).sum := by decide
  have hdescent : baseEnd_4910304 < baseStart_4910304 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910314 : List Nat := [3, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3]
def baseStart_4910314 : Nat := 118140960795 + 4910314 * 2 ^ 59
def prefixEnd_4910314 : Nat := 4983230072969 + 3 ^ 40 * 4910314 * 2
def baseEnd_4910314 : Nat := 2521351246501406607592883

theorem tailTrace_4910314 : CollatzResearch.WordTrace tailWord_4910314 prefixEnd_4910314 2521351246501406607592883 := by
  unfold tailWord_4910314
  simp only [CollatzResearch.WordTrace]
  refine ⟨44773466183194616927692499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119395909821852311807179997 44773466183194616927692499)
  ·
    refine ⟨67160199274791925391538749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 44773466183194616927692499 67160199274791925391538749)
    ·
      refine ⟨25185074728046972021827031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 67160199274791925391538749 25185074728046972021827031)
      ·
        refine ⟨37777612092070458032740547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25185074728046972021827031 37777612092070458032740547)
        ·
          refine ⟨56666418138105687049110821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37777612092070458032740547 56666418138105687049110821)
          ·
            refine ⟨10624953400894816321708279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56666418138105687049110821 10624953400894816321708279)
            ·
              refine ⟨15937430101342224482562419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10624953400894816321708279 15937430101342224482562419)
              ·
                refine ⟨23906145152013336723843629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 15937430101342224482562419 23906145152013336723843629)
                ·
                  refine ⟨8964804432005001271441361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 23906145152013336723843629 8964804432005001271441361)
                  ·
                    refine ⟨6723603324003750953581021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8964804432005001271441361 6723603324003750953581021)
                    ·
                      refine ⟨2521351246501406607592883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723603324003750953581021 2521351246501406607592883)
                      ·
                        rfl

theorem cell23_4910314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 1, 1, 3, 2, 3].length) (baseStart_4910314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910314 prefixEnd_4910314 := by exact prefixLift 4910314
  have htrace : WordTrace (prefixWord ++ tailWord_4910314) baseStart_4910314 baseEnd_4910314 := by
    simpa [prefixWord, tailWord_4910314, baseEnd_4910314] using wordTrace_append hprefix tailTrace_4910314
  have hstable : (prefixWord ++ tailWord_4910314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910314).length < 2 ^ (prefixWord ++ tailWord_4910314).sum := by decide
  have hdescent : baseEnd_4910314 < baseStart_4910314 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910317 : List Nat := [1, 5, 1, 2, 2, 1, 2, 9]
def baseStart_4910317 : Nat := 118140960795 + 4910317 * 2 ^ 59
def prefixEnd_4910317 : Nat := 4983230072969 + 3 ^ 40 * 4910317 * 2
def baseEnd_4910317 : Nat := 93383436553458151698347

theorem tailTrace_4910317 : CollatzResearch.WordTrace tailWord_4910317 prefixEnd_4910317 93383436553458151698347 := by
  unfold tailWord_4910317
  simp only [CollatzResearch.WordTrace]
  refine ⟨179093974151767599223129205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119395982767845066148752803 179093974151767599223129205)
  ·
    refine ⟨16790060076728212427168363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 179093974151767599223129205 16790060076728212427168363)
    ·
      refine ⟨25185090115092318640752545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 16790060076728212427168363 25185090115092318640752545)
      ·
        refine ⟨18888817586319238980564409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25185090115092318640752545 18888817586319238980564409)
        ·
          refine ⟨14166613189739429235423307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 18888817586319238980564409 14166613189739429235423307)
          ·
            refine ⟨21249919784609143853134961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14166613189739429235423307 21249919784609143853134961)
            ·
              refine ⟨15937439838456857889851221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21249919784609143853134961 15937439838456857889851221)
              ·
                refine ⟨93383436553458151698347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 15937439838456857889851221 93383436553458151698347)
                ·
                  rfl

theorem cell23_4910317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 2, 9].length) (baseStart_4910317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910317 prefixEnd_4910317 := by exact prefixLift 4910317
  have htrace : WordTrace (prefixWord ++ tailWord_4910317) baseStart_4910317 baseEnd_4910317 := by
    simpa [prefixWord, tailWord_4910317, baseEnd_4910317] using wordTrace_append hprefix tailTrace_4910317
  have hstable : (prefixWord ++ tailWord_4910317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910317).length < 2 ^ (prefixWord ++ tailWord_4910317).sum := by decide
  have hdescent : baseEnd_4910317 < baseStart_4910317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910327 : List Nat := [1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3]
def baseStart_4910327 : Nat := 118140960795 + 4910327 * 2 ^ 59
def prefixEnd_4910327 : Nat := 4983230072969 + 3 ^ 40 * 4910327 * 2
def baseEnd_4910327 : Nat := 2521357921749915056730323

theorem tailTrace_4910327 : CollatzResearch.WordTrace tailWord_4910327 prefixEnd_4910327 2521357921749915056730323 := by
  unfold tailWord_4910327
  simp only [CollatzResearch.WordTrace]
  refine ⟨179094338881731370930993235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119396225921154247287328823 179094338881731370930993235)
  ·
    refine ⟨268641508322597056396489853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179094338881731370930993235 268641508322597056396489853)
    ·
      refine ⟨100740565620973896148683695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268641508322597056396489853 100740565620973896148683695)
      ·
        refine ⟨151110848431460844223025543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100740565620973896148683695 151110848431460844223025543)
        ·
          refine ⟨226666272647191266334538315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151110848431460844223025543 226666272647191266334538315)
          ·
            refine ⟨339999408970786899501807473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226666272647191266334538315 339999408970786899501807473)
            ·
              refine ⟨254999556728090174626355605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 339999408970786899501807473 254999556728090174626355605)
              ·
                refine ⟨11953104221629226935610419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 254999556728090174626355605 11953104221629226935610419)
                ·
                  refine ⟨17929656332443840403415629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11953104221629226935610419 17929656332443840403415629)
                  ·
                    refine ⟨6723621124666440151280861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 17929656332443840403415629 6723621124666440151280861)
                    ·
                      refine ⟨2521357921749915056730323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6723621124666440151280861 2521357921749915056730323)
                      ·
                        rfl

theorem cell23_4910327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 6, 1, 3, 3].length) (baseStart_4910327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910327 prefixEnd_4910327 := by exact prefixLift 4910327
  have htrace : WordTrace (prefixWord ++ tailWord_4910327) baseStart_4910327 baseEnd_4910327 := by
    simpa [prefixWord, tailWord_4910327, baseEnd_4910327] using wordTrace_append hprefix tailTrace_4910327
  have hstable : (prefixWord ++ tailWord_4910327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910327).length < 2 ^ (prefixWord ++ tailWord_4910327).sum := by decide
  have hdescent : baseEnd_4910327 < baseStart_4910327 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910338 : List Nat := [3, 4, 1, 1, 3, 1, 2, 2, 2, 4]
def baseStart_4910338 : Nat := 118140960795 + 4910338 * 2 ^ 59
def prefixEnd_4910338 : Nat := 4983230072969 + 3 ^ 40 * 4910338 * 2
def baseEnd_4910338 : Nat := 840454523345704837897591

theorem tailTrace_4910338 : CollatzResearch.WordTrace tailWord_4910338 prefixEnd_4910338 840454523345704837897591 := by
  unfold tailWord_4910338
  simp only [CollatzResearch.WordTrace]
  refine ⟨44773685021172879952410917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 119396493389794346539762445 44773685021172879952410917)
  ·
    refine ⟨8395065941469914991077047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 44773685021172879952410917 8395065941469914991077047)
    ·
      refine ⟨12592598912204872486615571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8395065941469914991077047 12592598912204872486615571)
      ·
        refine ⟨18888898368307308729923357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12592598912204872486615571 18888898368307308729923357)
        ·
          refine ⟨7083336888115240773721259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 18888898368307308729923357 7083336888115240773721259)
          ·
            refine ⟨10625005332172861160581889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7083336888115240773721259 10625005332172861160581889)
            ·
              refine ⟨7968753999129645870436417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10625005332172861160581889 7968753999129645870436417)
              ·
                refine ⟨5976565499347234402827313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7968753999129645870436417 5976565499347234402827313)
                ·
                  refine ⟨4482424124510425802120485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5976565499347234402827313 4482424124510425802120485)
                  ·
                    refine ⟨840454523345704837897591, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4482424124510425802120485 840454523345704837897591)
                    ·
                      rfl

theorem cell23_4910338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_4910338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910338 prefixEnd_4910338 := by exact prefixLift 4910338
  have htrace : WordTrace (prefixWord ++ tailWord_4910338) baseStart_4910338 baseEnd_4910338 := by
    simpa [prefixWord, tailWord_4910338, baseEnd_4910338] using wordTrace_append hprefix tailTrace_4910338
  have hstable : (prefixWord ++ tailWord_4910338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910338).length < 2 ^ (prefixWord ++ tailWord_4910338).sum := by decide
  have hdescent : baseEnd_4910338 < baseStart_4910338 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910384 : List Nat := [2, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2]
def baseStart_4910384 : Nat := 118140960795 + 4910384 * 2 ^ 59
def prefixEnd_4910384 : Nat := 4983230072969 + 3 ^ 40 * 4910384 * 2
def baseEnd_4910384 : Nat := 2521387190147221333717561

theorem tailTrace_4910384 : CollatzResearch.WordTrace tailWord_4910384 prefixEnd_4910384 2521387190147221333717561 := by
  unfold tailWord_4910384
  simp only [CollatzResearch.WordTrace]
  refine ⟨89548208921262434832909103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119397611895016579777212137 89548208921262434832909103)
  ·
    refine ⟨134322313381893652249363655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89548208921262434832909103 134322313381893652249363655)
    ·
      refine ⟨201483470072840478374045483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134322313381893652249363655 201483470072840478374045483)
      ·
        refine ⟨302225205109260717561068225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201483470072840478374045483 302225205109260717561068225)
        ·
          refine ⟨226668903831945538170801169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302225205109260717561068225 226668903831945538170801169)
          ·
            refine ⟨170001677873959153628100877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 226668903831945538170801169 170001677873959153628100877)
            ·
              refine ⟨63750629202734682610537829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 170001677873959153628100877 63750629202734682610537829)
              ·
                refine ⟨11953242975512752989475843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 63750629202734682610537829 11953242975512752989475843)
                ·
                  refine ⟨17929864463269129484213765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11953242975512752989475843 17929864463269129484213765)
                  ·
                    refine ⟨3361849586862961778290081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 17929864463269129484213765 3361849586862961778290081)
                    ·
                      refine ⟨2521387190147221333717561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361849586862961778290081 2521387190147221333717561)
                      ·
                        rfl

theorem cell23_4910384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 4, 1, 4, 2].length) (baseStart_4910384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910384 prefixEnd_4910384 := by exact prefixLift 4910384
  have htrace : WordTrace (prefixWord ++ tailWord_4910384) baseStart_4910384 baseEnd_4910384 := by
    simpa [prefixWord, tailWord_4910384, baseEnd_4910384] using wordTrace_append hprefix tailTrace_4910384
  have hstable : (prefixWord ++ tailWord_4910384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910384).length < 2 ^ (prefixWord ++ tailWord_4910384).sum := by decide
  have hdescent : baseEnd_4910384 < baseStart_4910384 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910388 : List Nat := [2, 5, 1, 1, 1, 1, 3, 3, 1, 3, 2]
def baseStart_4910388 : Nat := 118140960795 + 4910388 * 2 ^ 59
def prefixEnd_4910388 : Nat := 4983230072969 + 3 ^ 40 * 4910388 * 2
def baseEnd_4910388 : Nat := 2521389244069839318067543

theorem tailTrace_4910388 : CollatzResearch.WordTrace tailWord_4910388 prefixEnd_4910388 2521389244069839318067543 := by
  unfold tailWord_4910388
  simp only [CollatzResearch.WordTrace]
  refine ⟨89548281867255189174481909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119397709156340252232642545 89548281867255189174481909)
  ·
    refine ⟨8395151425055173985107679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 89548281867255189174481909 8395151425055173985107679)
    ·
      refine ⟨12592727137582760977661519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8395151425055173985107679 12592727137582760977661519)
      ·
        refine ⟨18889090706374141466492279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12592727137582760977661519 18889090706374141466492279)
        ·
          refine ⟨28333636059561212199738419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 18889090706374141466492279 28333636059561212199738419)
          ·
            refine ⟨42500454089341818299607629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28333636059561212199738419 42500454089341818299607629)
            ·
              refine ⟨15937670283503181862352861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 42500454089341818299607629 15937670283503181862352861)
              ·
                refine ⟨5976626356313693198382323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15937670283503181862352861 5976626356313693198382323)
                ·
                  refine ⟨8964939534470539797573485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5976626356313693198382323 8964939534470539797573485)
                  ·
                    refine ⟨3361852325426452424090057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8964939534470539797573485 3361852325426452424090057)
                    ·
                      refine ⟨2521389244069839318067543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3361852325426452424090057 2521389244069839318067543)
                      ·
                        rfl

theorem cell23_4910388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 3, 3, 1, 3, 2].length) (baseStart_4910388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910388 prefixEnd_4910388 := by exact prefixLift 4910388
  have htrace : WordTrace (prefixWord ++ tailWord_4910388) baseStart_4910388 baseEnd_4910388 := by
    simpa [prefixWord, tailWord_4910388, baseEnd_4910388] using wordTrace_append hprefix tailTrace_4910388
  have hstable : (prefixWord ++ tailWord_4910388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910388).length < 2 ^ (prefixWord ++ tailWord_4910388).sum := by decide
  have hdescent : baseEnd_4910388 < baseStart_4910388 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910407 : List Nat := [1, 1, 4, 1, 2, 3, 1, 3, 7]
def baseStart_4910407 : Nat := 118140960795 + 4910407 * 2 ^ 59
def prefixEnd_4910407 : Nat := 4983230072969 + 3 ^ 40 * 4910407 * 2
def baseEnd_4910407 : Nat := 280155444466919415969995

theorem tailTrace_4910407 : CollatzResearch.WordTrace tailWord_4910407 prefixEnd_4910407 280155444466919415969995 := by
  unfold tailWord_4910407
  simp only [CollatzResearch.WordTrace]
  refine ⟨179097256721441544593905475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119398171147627696395936983 179097256721441544593905475)
  ·
    refine ⟨268645885082162316890858213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179097256721441544593905475 268645885082162316890858213)
    ·
      refine ⟨50371103452905434417035915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 268645885082162316890858213 50371103452905434417035915)
      ·
        refine ⟨75556655179358151625553873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50371103452905434417035915 75556655179358151625553873)
        ·
          refine ⟨56667491384518613719165405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75556655179358151625553873 56667491384518613719165405)
          ·
            refine ⟨21250309269194480144687027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56667491384518613719165405 21250309269194480144687027)
            ·
              refine ⟨31875463903791720217030541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21250309269194480144687027 31875463903791720217030541)
              ·
                refine ⟨11953298963921895081386453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 31875463903791720217030541 11953298963921895081386453)
                ·
                  refine ⟨280155444466919415969995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11953298963921895081386453 280155444466919415969995)
                  ·
                    rfl

theorem cell23_4910407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 3, 7].length) (baseStart_4910407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910407 prefixEnd_4910407 := by exact prefixLift 4910407
  have htrace : WordTrace (prefixWord ++ tailWord_4910407) baseStart_4910407 baseEnd_4910407 := by
    simpa [prefixWord, tailWord_4910407, baseEnd_4910407] using wordTrace_append hprefix tailTrace_4910407
  have hstable : (prefixWord ++ tailWord_4910407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910407).length < 2 ^ (prefixWord ++ tailWord_4910407).sum := by decide
  have hdescent : baseEnd_4910407 < baseStart_4910407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910437 : List Nat := [1, 3, 1, 3, 1, 2, 1, 3, 1, 7]
def baseStart_4910437 : Nat := 118140960795 + 4910437 * 2 ^ 59
def prefixEnd_4910437 : Nat := 4983230072969 + 3 ^ 40 * 4910437 * 2
def baseEnd_4910437 : Nat := 840471468207303208784939

theorem tailTrace_4910437 : CollatzResearch.WordTrace tailWord_4910437 prefixEnd_4910437 840471468207303208784939 := by
  unfold tailWord_4910437
  simp only [CollatzResearch.WordTrace]
  refine ⟨179098350911332859717497565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119398900607555239811665043 179098350911332859717497565)
  ·
    refine ⟨67161881591749822394061587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179098350911332859717497565 67161881591749822394061587)
    ·
      refine ⟨100742822387624733591092381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 67161881591749822394061587 100742822387624733591092381)
      ·
        refine ⟨37778558395359275096659643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100742822387624733591092381 37778558395359275096659643)
        ·
          refine ⟨56667837593038912644989465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37778558395359275096659643 56667837593038912644989465)
          ·
            refine ⟨42500878194779184483742099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 56667837593038912644989465 42500878194779184483742099)
            ·
              refine ⟨63751317292168776725613149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 42500878194779184483742099 63751317292168776725613149)
              ·
                refine ⟨23906743984563291272104931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 63751317292168776725613149 23906743984563291272104931)
                ·
                  refine ⟨35860115976844936908157397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23906743984563291272104931 35860115976844936908157397)
                  ·
                    refine ⟨840471468207303208784939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 35860115976844936908157397 840471468207303208784939)
                    ·
                      rfl

theorem cell23_4910437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 1, 7].length) (baseStart_4910437 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910437 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910437 prefixEnd_4910437 := by exact prefixLift 4910437
  have htrace : WordTrace (prefixWord ++ tailWord_4910437) baseStart_4910437 baseEnd_4910437 := by
    simpa [prefixWord, tailWord_4910437, baseEnd_4910437] using wordTrace_append hprefix tailTrace_4910437
  have hstable : (prefixWord ++ tailWord_4910437).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910437).length < 2 ^ (prefixWord ++ tailWord_4910437).sum := by decide
  have hdescent : baseEnd_4910437 < baseStart_4910437 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910447 : List Nat := [1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5]
def baseStart_4910447 : Nat := 118140960795 + 4910447 * 2 ^ 59
def prefixEnd_4910447 : Nat := 4983230072969 + 3 ^ 40 * 4910447 * 2
def baseEnd_4910447 : Nat := 2521419539428454587229771

theorem tailTrace_4910447 : CollatzResearch.WordTrace tailWord_4910447 prefixEnd_4910447 2521419539428454587229771 := by
  unfold tailWord_4910447
  simp only [CollatzResearch.WordTrace]
  refine ⟨179098715641296631425361595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119399143760864420950241063 179098715641296631425361595)
  ·
    refine ⟨268648073461944947138042393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179098715641296631425361595 268648073461944947138042393)
    ·
      refine ⟨201486055096458710353531795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 268648073461944947138042393 201486055096458710353531795)
      ·
        refine ⟨302229082644688065530297693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201486055096458710353531795 302229082644688065530297693)
        ·
          refine ⟨113335905991758024573861635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 302229082644688065530297693 113335905991758024573861635)
          ·
            refine ⟨170003858987637036860792453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113335905991758024573861635 170003858987637036860792453)
            ·
              refine ⟨31875723560181944411398585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 170003858987637036860792453 31875723560181944411398585)
              ·
                refine ⟨23906792670136458308548939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 31875723560181944411398585 23906792670136458308548939)
                ·
                  refine ⟨35860189005204687462823409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 23906792670136458308548939 35860189005204687462823409)
                  ·
                    refine ⟨26895141753903515597117557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 35860189005204687462823409 26895141753903515597117557)
                    ·
                      refine ⟨2521419539428454587229771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26895141753903515597117557 2521419539428454587229771)
                      ·
                        rfl

theorem cell23_4910447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 2, 1, 2, 5].length) (baseStart_4910447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910447 prefixEnd_4910447 := by exact prefixLift 4910447
  have htrace : WordTrace (prefixWord ++ tailWord_4910447) baseStart_4910447 baseEnd_4910447 := by
    simpa [prefixWord, tailWord_4910447, baseEnd_4910447] using wordTrace_append hprefix tailTrace_4910447
  have hstable : (prefixWord ++ tailWord_4910447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910447).length < 2 ^ (prefixWord ++ tailWord_4910447).sum := by decide
  have hdescent : baseEnd_4910447 < baseStart_4910447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910487 : List Nat := [1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6]
def baseStart_4910487 : Nat := 118140960795 + 4910487 * 2 ^ 59
def prefixEnd_4910487 : Nat := 4983230072969 + 3 ^ 40 * 4910487 * 2
def baseEnd_4910487 : Nat := 2521440078654634430729587

theorem tailTrace_4910487 : CollatzResearch.WordTrace tailWord_4910487 prefixEnd_4910487 2521440078654634430729587 := by
  unfold tailWord_4910487
  simp only [CollatzResearch.WordTrace]
  refine ⟨179100174561151718256817715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119400116374101145504545143 179100174561151718256817715)
  ·
    refine ⟨268650261841727577385226573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179100174561151718256817715 268650261841727577385226573)
    ·
      refine ⟨100743848190647841519459965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 268650261841727577385226573 100743848190647841519459965)
      ·
        refine ⟨37778943071492940569797487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100743848190647841519459965 37778943071492940569797487)
        ·
          refine ⟨56668414607239410854696231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37778943071492940569797487 56668414607239410854696231)
          ·
            refine ⟨85002621910859116282044347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56668414607239410854696231 85002621910859116282044347)
            ·
              refine ⟨127503932866288674423066521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85002621910859116282044347 127503932866288674423066521)
              ·
                refine ⟨95627949649716505817299891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 127503932866288674423066521 95627949649716505817299891)
                ·
                  refine ⟨143441924474574758725949837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 95627949649716505817299891 143441924474574758725949837)
                  ·
                    refine ⟨53790721677965534522231189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 143441924474574758725949837 53790721677965534522231189)
                    ·
                      refine ⟨2521440078654634430729587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 53790721677965534522231189 2521440078654634430729587)
                      ·
                        rfl

theorem cell23_4910487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_4910487 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910487 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910487 prefixEnd_4910487 := by exact prefixLift 4910487
  have htrace : WordTrace (prefixWord ++ tailWord_4910487) baseStart_4910487 baseEnd_4910487 := by
    simpa [prefixWord, tailWord_4910487, baseEnd_4910487] using wordTrace_append hprefix tailTrace_4910487
  have hstable : (prefixWord ++ tailWord_4910487).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910487).length < 2 ^ (prefixWord ++ tailWord_4910487).sum := by decide
  have hdescent : baseEnd_4910487 < baseStart_4910487 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910537 : List Nat := [1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 7]
def baseStart_4910537 : Nat := 118140960795 + 4910537 * 2 ^ 59
def prefixEnd_4910537 : Nat := 4983230072969 + 3 ^ 40 * 4910537 * 2
def baseEnd_4910537 : Nat := 2521465752687359235104357

theorem tailTrace_4910537 : CollatzResearch.WordTrace tailWord_4910537 prefixEnd_4910537 2521465752687359235104357 := by
  unfold tailWord_4910537
  simp only [CollatzResearch.WordTrace]
  refine ⟨179101998210970576796137865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119401332140647051197425243 179101998210970576796137865)
  ·
    refine ⟨134326498658227932597103399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179101998210970576796137865 134326498658227932597103399)
    ·
      refine ⟨201489747987341898895655099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 134326498658227932597103399 201489747987341898895655099)
      ·
        refine ⟨302234621981012848343482649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 201489747987341898895655099 302234621981012848343482649)
        ·
          refine ⟨226675966485759636257611987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 302234621981012848343482649 226675966485759636257611987)
          ·
            refine ⟨340013949728639454386417981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 226675966485759636257611987 340013949728639454386417981)
            ·
              refine ⟨127505231148239795394906743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 340013949728639454386417981 127505231148239795394906743)
              ·
                refine ⟨191257846722359693092360115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127505231148239795394906743 191257846722359693092360115)
                ·
                  refine ⟨286886770083539539638540173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 191257846722359693092360115 286886770083539539638540173)
                  ·
                    refine ⟨107582538781327327364452565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 286886770083539539638540173 107582538781327327364452565)
                    ·
                      refine ⟨2521465752687359235104357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 107582538781327327364452565 2521465752687359235104357)
                      ·
                        rfl

theorem cell23_4910537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 1, 1, 3, 7].length) (baseStart_4910537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910537 prefixEnd_4910537 := by exact prefixLift 4910537
  have htrace : WordTrace (prefixWord ++ tailWord_4910537) baseStart_4910537 baseEnd_4910537 := by
    simpa [prefixWord, tailWord_4910537, baseEnd_4910537] using wordTrace_append hprefix tailTrace_4910537
  have hstable : (prefixWord ++ tailWord_4910537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910537).length < 2 ^ (prefixWord ++ tailWord_4910537).sum := by decide
  have hdescent : baseEnd_4910537 < baseStart_4910537 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910561 : List Nat := [1, 2, 3, 1, 2, 4, 1, 3, 1, 5]
def baseStart_4910561 : Nat := 118140960795 + 4910561 * 2 ^ 59
def prefixEnd_4910561 : Nat := 4983230072969 + 3 ^ 40 * 4910561 * 2
def baseEnd_4910561 : Nat := 840492692074355713734749

theorem tailTrace_4910561 : CollatzResearch.WordTrace tailWord_4910561 prefixEnd_4910561 840492692074355713734749 := by
  unfold tailWord_4910561
  simp only [CollatzResearch.WordTrace]
  refine ⟨179102873562883628895011537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119401915708589085930007691 179102873562883628895011537)
  ·
    refine ⟨134327155172162721671258653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179102873562883628895011537 134327155172162721671258653)
    ·
      refine ⟨50372683189561020626721995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134327155172162721671258653 50372683189561020626721995)
      ·
        refine ⟨75559024784341530940082993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50372683189561020626721995 75559024784341530940082993)
        ·
          refine ⟨56669268588256148205062245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 75559024784341530940082993 56669268588256148205062245)
          ·
            refine ⟨10625487860298027788449171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 56669268588256148205062245 10625487860298027788449171)
            ·
              refine ⟨15938231790447041682673757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10625487860298027788449171 15938231790447041682673757)
              ·
                refine ⟨5976836921417640631002659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 15938231790447041682673757 5976836921417640631002659)
                ·
                  refine ⟨8965255382126460946503989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5976836921417640631002659 8965255382126460946503989)
                  ·
                    refine ⟨840492692074355713734749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8965255382126460946503989 840492692074355713734749)
                    ·
                      rfl

theorem cell23_4910561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_4910561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910561 prefixEnd_4910561 := by exact prefixLift 4910561
  have htrace : WordTrace (prefixWord ++ tailWord_4910561) baseStart_4910561 baseEnd_4910561 := by
    simpa [prefixWord, tailWord_4910561, baseEnd_4910561] using wordTrace_append hprefix tailTrace_4910561
  have hstable : (prefixWord ++ tailWord_4910561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910561).length < 2 ^ (prefixWord ++ tailWord_4910561).sum := by decide
  have hdescent : baseEnd_4910561 < baseStart_4910561 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910584 : List Nat := [2, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5]
def baseStart_4910584 : Nat := 118140960795 + 4910584 * 2 ^ 59
def prefixEnd_4910584 : Nat := 4983230072969 + 3 ^ 40 * 4910584 * 2
def baseEnd_4910584 : Nat := 2521489886278120551216641

theorem tailTrace_4910584 : CollatzResearch.WordTrace tailWord_4910584 prefixEnd_4910584 2521489886278120551216641 := by
  unfold tailWord_4910584
  simp only [CollatzResearch.WordTrace]
  refine ⟨89551856220900151911549403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119402474961200202548732537 89551856220900151911549403)
  ·
    refine ⟨134327784331350227867324105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89551856220900151911549403 134327784331350227867324105)
    ·
      refine ⟨100745838248512670900493079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134327784331350227867324105 100745838248512670900493079)
      ·
        refine ⟨151118757372769006350739619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 100745838248512670900493079 151118757372769006350739619)
        ·
          refine ⟨226678136059153509526109429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 151118757372769006350739619 226678136059153509526109429)
          ·
            refine ⟨21251075255545641518072759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 226678136059153509526109429 21251075255545641518072759)
            ·
              refine ⟨31876612883318462277109139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21251075255545641518072759 31876612883318462277109139)
              ·
                refine ⟨47814919324977693415663709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31876612883318462277109139 47814919324977693415663709)
                ·
                  refine ⟨17930594746866635030873891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 47814919324977693415663709 17930594746866635030873891)
                  ·
                    refine ⟨26895892120299952546310837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 17930594746866635030873891 26895892120299952546310837)
                    ·
                      refine ⟨2521489886278120551216641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 26895892120299952546310837 2521489886278120551216641)
                      ·
                        rfl

theorem cell23_4910584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_4910584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910584 prefixEnd_4910584 := by exact prefixLift 4910584
  have htrace : WordTrace (prefixWord ++ tailWord_4910584) baseStart_4910584 baseEnd_4910584 := by
    simpa [prefixWord, tailWord_4910584, baseEnd_4910584] using wordTrace_append hprefix tailTrace_4910584
  have hstable : (prefixWord ++ tailWord_4910584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910584).length < 2 ^ (prefixWord ++ tailWord_4910584).sum := by decide
  have hdescent : baseEnd_4910584 < baseStart_4910584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910641 : List Nat := [1, 2, 2, 3, 1, 1, 1, 1, 2, 7, 2]
def baseStart_4910641 : Nat := 118140960795 + 4910641 * 2 ^ 59
def prefixEnd_4910641 : Nat := 4983230072969 + 3 ^ 40 * 4910641 * 2
def baseEnd_4910641 : Nat := 2521519154675426828203879

theorem tailTrace_4910641 : CollatzResearch.WordTrace tailWord_4910641 prefixEnd_4910641 2521519154675426828203879 := by
  unfold tailWord_4910641
  simp only [CollatzResearch.WordTrace]
  refine ⟨179105791402593802557923777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119403860935062535038615851 179105791402593802557923777)
  ·
    refine ⟨134329343551945351918442833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 179105791402593802557923777 134329343551945351918442833)
    ·
      refine ⟨100747007663959013938832125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 134329343551945351918442833 100747007663959013938832125)
      ·
        refine ⟨37780127873984630227062047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 100747007663959013938832125 37780127873984630227062047)
        ·
          refine ⟨56670191810976945340593071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37780127873984630227062047 56670191810976945340593071)
          ·
            refine ⟨85005287716465418010889607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 56670191810976945340593071 85005287716465418010889607)
            ·
              refine ⟨127507931574698127016334411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 85005287716465418010889607 127507931574698127016334411)
              ·
                refine ⟨191261897362047190524501617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 127507931574698127016334411 191261897362047190524501617)
                ·
                  refine ⟨143446423021535392893376213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 191261897362047190524501617 143446423021535392893376213)
                  ·
                    refine ⟨3362025539567235770938505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 143446423021535392893376213 3362025539567235770938505)
                    ·
                      refine ⟨2521519154675426828203879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3362025539567235770938505 2521519154675426828203879)
                      ·
                        rfl

theorem cell23_4910641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 1, 2, 7, 2].length) (baseStart_4910641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910641 prefixEnd_4910641 := by exact prefixLift 4910641
  have htrace : WordTrace (prefixWord ++ tailWord_4910641) baseStart_4910641 baseEnd_4910641 := by
    simpa [prefixWord, tailWord_4910641, baseEnd_4910641] using wordTrace_append hprefix tailTrace_4910641
  have hstable : (prefixWord ++ tailWord_4910641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910641).length < 2 ^ (prefixWord ++ tailWord_4910641).sum := by decide
  have hdescent : baseEnd_4910641 < baseStart_4910641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910652 : List Nat := [2, 2, 2, 2, 5, 1, 1, 2, 1, 2, 3]
def baseStart_4910652 : Nat := 118140960795 + 4910652 * 2 ^ 59
def prefixEnd_4910652 : Nat := 4983230072969 + 3 ^ 40 * 4910652 * 2
def baseEnd_4910652 : Nat := 2521524802962626285166329

theorem tailTrace_4910652 : CollatzResearch.WordTrace tailWord_4910652 prefixEnd_4910652 2521524802962626285166329 := by
  unfold tailWord_4910652
  simp only [CollatzResearch.WordTrace]
  refine ⟨89553096302776975718287105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119404128403702634291049473 89553096302776975718287105)
  ·
    refine ⟨67164822227082731788715329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 89553096302776975718287105 67164822227082731788715329)
    ·
      refine ⟨50373616670312048841536497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67164822227082731788715329 50373616670312048841536497)
      ·
        refine ⟨37780212502734036631152373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 50373616670312048841536497 37780212502734036631152373)
        ·
          refine ⟨3541894922131315934170535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 37780212502734036631152373 3541894922131315934170535)
          ·
            refine ⟨5312842383196973901255803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3541894922131315934170535 5312842383196973901255803)
            ·
              refine ⟨7969263574795460851883705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5312842383196973901255803 7969263574795460851883705)
              ·
                refine ⟨5976947681096595638912779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7969263574795460851883705 5976947681096595638912779)
                ·
                  refine ⟨8965421521644893458369169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5976947681096595638912779 8965421521644893458369169)
                  ·
                    refine ⟨6724066141233670093776877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8965421521644893458369169 6724066141233670093776877)
                    ·
                      refine ⟨2521524802962626285166329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6724066141233670093776877 2521524802962626285166329)
                      ·
                        rfl

theorem cell23_4910652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 2, 1, 2, 3].length) (baseStart_4910652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910652 prefixEnd_4910652 := by exact prefixLift 4910652
  have htrace : WordTrace (prefixWord ++ tailWord_4910652) baseStart_4910652 baseEnd_4910652 := by
    simpa [prefixWord, tailWord_4910652, baseEnd_4910652] using wordTrace_append hprefix tailTrace_4910652
  have hstable : (prefixWord ++ tailWord_4910652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910652).length < 2 ^ (prefixWord ++ tailWord_4910652).sum := by decide
  have hdescent : baseEnd_4910652 < baseStart_4910652 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910664 : List Nat := [2, 1, 3, 1, 1, 1, 1, 1, 6, 6]
def baseStart_4910664 : Nat := 118140960795 + 4910664 * 2 ^ 59
def prefixEnd_4910664 : Nat := 4983230072969 + 3 ^ 40 * 4910664 * 2
def baseEnd_4910664 : Nat := 840510321576826746072091

theorem tailTrace_4910664 : CollatzResearch.WordTrace tailWord_4910664 prefixEnd_4910664 840510321576826746072091 := by
  unfold tailWord_4910664
  simp only [CollatzResearch.WordTrace]
  refine ⟨89553315140755238743005523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 119404420187673651657340697 89553315140755238743005523)
  ·
    refine ⟨134329972711132858114508285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 89553315140755238743005523 134329972711132858114508285)
    ·
      refine ⟨50373739766674821792940607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 134329972711132858114508285 50373739766674821792940607)
      ·
        refine ⟨75560609650012232689410911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50373739766674821792940607 75560609650012232689410911)
        ·
          refine ⟨113340914475018349034116367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75560609650012232689410911 113340914475018349034116367)
          ·
            refine ⟨170011371712527523551174551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113340914475018349034116367 170011371712527523551174551)
            ·
              refine ⟨255017057568791285326761827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170011371712527523551174551 255017057568791285326761827)
              ·
                refine ⟨382525586353186927990142741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 255017057568791285326761827 382525586353186927990142741)
                ·
                  refine ⟨17930886860305637249537941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 382525586353186927990142741 17930886860305637249537941)
                  ·
                    refine ⟨840510321576826746072091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 17930886860305637249537941 840510321576826746072091)
                    ·
                      rfl

theorem cell23_4910664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 6, 6].length) (baseStart_4910664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910664 prefixEnd_4910664 := by exact prefixLift 4910664
  have htrace : WordTrace (prefixWord ++ tailWord_4910664) baseStart_4910664 baseEnd_4910664 := by
    simpa [prefixWord, tailWord_4910664, baseEnd_4910664] using wordTrace_append hprefix tailTrace_4910664
  have hstable : (prefixWord ++ tailWord_4910664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910664).length < 2 ^ (prefixWord ++ tailWord_4910664).sum := by decide
  have hdescent : baseEnd_4910664 < baseStart_4910664 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910691 : List Nat := [1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3]
def baseStart_4910691 : Nat := 118140960795 + 4910691 * 2 ^ 59
def prefixEnd_4910691 : Nat := 4983230072969 + 3 ^ 40 * 4910691 * 2
def baseEnd_4910691 : Nat := 2521544828708151632578649

theorem tailTrace_4910691 : CollatzResearch.WordTrace tailWord_4910691 prefixEnd_4910691 2521544828708151632578649 := by
  unfold tailWord_4910691
  simp only [CollatzResearch.WordTrace]
  refine ⟨179107615052412661097243927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119405076701608440731495951 179107615052412661097243927)
  ·
    refine ⟨268661422578618991645865891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 179107615052412661097243927 268661422578618991645865891)
    ·
      refine ⟨402992133867928487468798837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 268661422578618991645865891 402992133867928487468798837)
      ·
        refine ⟨37780512550118295700199891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 402992133867928487468798837 37780512550118295700199891)
        ·
          refine ⟨56670768825177443550299837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 37780512550118295700199891 56670768825177443550299837)
          ·
            refine ⟨21251538309441541331362439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 56670768825177443550299837 21251538309441541331362439)
            ·
              refine ⟨31877307464162311997043659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21251538309441541331362439 31877307464162311997043659)
              ·
                refine ⟨47815961196243467995565489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 31877307464162311997043659 47815961196243467995565489)
                ·
                  refine ⟨35861970897182600996674117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 47815961196243467995565489 35861970897182600996674117)
                  ·
                    refine ⟨6724119543221737686876397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 35861970897182600996674117 6724119543221737686876397)
                    ·
                      refine ⟨2521544828708151632578649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6724119543221737686876397 2521544828708151632578649)
                      ·
                        rfl

theorem cell23_4910691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 1, 2, 4, 3].length) (baseStart_4910691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910691 prefixEnd_4910691 := by exact prefixLift 4910691
  have htrace : WordTrace (prefixWord ++ tailWord_4910691) baseStart_4910691 baseEnd_4910691 := by
    simpa [prefixWord, tailWord_4910691, baseEnd_4910691] using wordTrace_append hprefix tailTrace_4910691
  have hstable : (prefixWord ++ tailWord_4910691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910691).length < 2 ^ (prefixWord ++ tailWord_4910691).sum := by decide
  have hdescent : baseEnd_4910691 < baseStart_4910691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4910741 : List Nat := [1, 3, 2, 1, 1, 1, 1, 6, 2, 5]
def baseStart_4910741 : Nat := 118140960795 + 4910741 * 2 ^ 59
def prefixEnd_4910741 : Nat := 4983230072969 + 3 ^ 40 * 4910741 * 2
def baseEnd_4910741 : Nat := 840523500913625478984473

theorem tailTrace_4910741 : CollatzResearch.WordTrace tailWord_4910741 prefixEnd_4910741 840523500913625478984473 := by
  unfold tailWord_4910741
  simp only [CollatzResearch.WordTrace]
  refine ⟨179109438702231519636564077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 119406292468154346424376051 179109438702231519636564077)
  ·
    refine ⟨67166039513336819863711529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 179109438702231519636564077 67166039513336819863711529)
    ·
      refine ⟨50374529635002614897783647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 67166039513336819863711529 50374529635002614897783647)
      ·
        refine ⟨75561794452503922346675471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 50374529635002614897783647 75561794452503922346675471)
        ·
          refine ⟨113342691678755883520013207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 75561794452503922346675471 113342691678755883520013207)
          ·
            refine ⟨170014037518133825280019811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 113342691678755883520013207 170014037518133825280019811)
            ·
              refine ⟨255021056277200737920029717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 170014037518133825280019811 255021056277200737920029717)
              ·
                refine ⟨11954112012993784590001393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 255021056277200737920029717 11954112012993784590001393)
                ·
                  refine ⟨8965584009745338442501045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11954112012993784590001393 8965584009745338442501045)
                  ·
                    refine ⟨840523500913625478984473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8965584009745338442501045 840523500913625478984473)
                    ·
                      rfl

theorem cell23_4910741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 6, 2, 5].length) (baseStart_4910741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4910741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4910741 prefixEnd_4910741 := by exact prefixLift 4910741
  have htrace : WordTrace (prefixWord ++ tailWord_4910741) baseStart_4910741 baseEnd_4910741 := by
    simpa [prefixWord, tailWord_4910741, baseEnd_4910741] using wordTrace_append hprefix tailTrace_4910741
  have hstable : (prefixWord ++ tailWord_4910741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4910741).length < 2 ^ (prefixWord ++ tailWord_4910741).sum := by decide
  have hdescent : baseEnd_4910741 < baseStart_4910741 := by decide
  rcases family_descends (prefixWord ++ tailWord_4910741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
